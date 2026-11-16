-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spectrallyNegativeDescendingLadderHeightTriplet
-- name    : Kyprianou.Ch06.spectrallyNegativeDescendingLadderHeightTriplet
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:17:45.425987+00:00
-- url     : https://prove2.me/theorems/da23a752-1e41-4221-a546-41deb9aa581b
-- title:
--   Exercise 6.5: descending ladder height Lévy triplet
-- statement:
--   For a spectrally negative Lévy process with finite strictly positive E(X₁) and its genuine dual descending ladder process: (i) prove finiteness of ∫_{−∞}^{−1}Π(−∞,x)dx; (ii) using the Wiener–Hopf factorisation, obtain the displayed Fourier exponent for the descending ladder process, including its Gaussian and integrated negative-tail terms, up to a positive local-time normalisation; and identify the descending ladder-height jump density Π(−∞,−y)dy, drift σ²/2 and killing rate E(X₁) after that normalisation. Check source Fourier sign conventions independently before submission.
-- source:
--   Kyprianou (2006), Exercise 6.5(i)–(ii), printed pp. 175–176; physical two-up PDF pp. 93–94.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.5: finite integrated negative jump tails, the
explicit Fourier exponent for the descending ladder-height process,
and the Levy measure, Gaussian drift and killing rate of that process
after a choice of maximum-local-time normalisation. -/
theorem spectrallyNegativeDescendingLadderHeightTriplet
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Ldown : NNReal → Omega → NNReal)
    (b mu : Real) (sigma2 : NNReal) (nu : Measure Real)
    (nuDesc : Measure NNReal)
    (driftDesc killDesc : NNReal)
    (hatKappa : Complex → Complex)
    (hX : IsRealLevyProcess P X)
    (hTriplet : IsLevyKhintchineTriplet P X b sigma2 nu)
    (hNoPositiveJumps : nu (Set.Ioi 0) = 0)
    (hMean : Integrable (X 1) P ∧
      (∫ omega, X 1 omega ∂P) = mu ∧ 0 < mu)
    (hDescLocal : IsAdmissibleLocalTimeAtMaximum P F
      (fun t omega => -X t omega) Ldown)
    (hDescLaw : ∀ (t beta : NNReal),
      (∫ omega,
        let tau := inverseLocalTime Ldown t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-(beta : Real) *
          runningMaximum (fun s w => -X s w)
            (tau.untopD 0) omega) ∂P) =
        Real.exp (-(t : Real) *
          (hatKappa (↑(beta : Real) : Complex)).re))
    (hHatTriplet : ∀ beta : NNReal,
      hatKappa (↑(beta : Real) : Complex) =
        (↑((killDesc : Real) +
          (driftDesc : Real) * (beta : Real)) : Complex) +
        ↑((∫⁻ y : NNReal,
          ENNReal.ofReal
            (1 - Real.exp (-(beta : Real) * (y : Real)))
          ∂nuDesc).toReal)) :
    -- (i) Integrated negative-tail mass is finite
    ((∫⁻ x in Set.Iio (-1 : Real),
      nu (Set.Iio x) ∂volume) < ⊤) ∧
    -- (ii) Descending Fourier exponent, with its source sign convention
    (∃ c : Real, 0 < c ∧
      (∀ theta : Real,
        hatKappa (Complex.I * (↑theta : Complex)) =
          (↑c : Complex) *
            ((↑mu : Complex) -
              Complex.I * (↑(theta * (sigma2 : Real) / 2) : Complex) +
              ∫ x in Set.Iio (0 : Real),
                (1 - Complex.exp (Complex.I *
                   (↑(theta * x) : Complex))) *
                (↑((nu (Set.Iio x)).toReal) : Complex) ∂volume)) ∧
      -- A positive deterministic rescaling of local time makes the
      -- descending height jump law nu(-infinity,-y)dy and drift sigma2/2
      -- with killing rate mu
      (∀ A : Set NNReal, MeasurableSet A →
        nuDesc A =
          ENNReal.ofReal c *
            (∫⁻ y in A ∩ Set.Ioi (0 : NNReal),
              nu (Set.Iio (-(y : Real))) ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real)))))) ∧
      (driftDesc : Real) = c * ((sigma2 : Real) / 2) ∧
      (killDesc : Real) = c * mu) := by
  sorry

end Kyprianou.Ch06
