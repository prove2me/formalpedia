-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spectrallyNegativeStablePositivityAndSupremum
-- name    : Kyprianou.Ch06.spectrallyNegativeStablePositivityAndSupremum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:09:21.331495+00:00
-- url     : https://prove2.me/theorems/51cc7077-cf7f-49b1-9145-e5fee33a0de6
-- title:
--   Exercise 6.6: stable positivity and the supremum Mittag-Leffler transform
-- statement:
--   For a spectrally negative stable Lévy process of index 1<α<2 normalised to Laplace exponent ψ(λ)=λ^α, show (i) that the ascending ladder-time exponent is proportional to θ^(1/α) and P(X_t≥0)=1/α for each t>0, and (ii) that E exp(-θ sup_{s≤t}X_s) equals the convergent Mittag-Leffler series Σₙ(-θ t^(1/α))^n/Γ(1+n/α). Correct the printed t≥0 positivity claim at t=0; retain the full t≥0 transform claim.
-- source:
--   Kyprianou (2006), Exercise 6.6(i)–(ii), printed p. 176; two-up PDF p. 93. T=0 boundary correction documented in source issues.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.6: a spectrally negative stable Levy process of index
1 < alpha < 2 and unit Laplace scale. The ascending ladder-time
exponent has power 1/alpha up to local-time normalisation, the
positivity probability is 1/alpha at every STRICTLY positive time,
and the supremum has the Mittag-Leffler Laplace transform. -/
theorem spectrallyNegativeStablePositivityAndSupremum
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (alpha : Real) (kappa : NNReal → Real)
    (hAlpha : 1 < alpha ∧ alpha < 2)
    (hX : IsRealLevyProcess P X)
    (hStable : ∀ (t : NNReal) (lambda : Real), 0 ≤ lambda →
      (∫ omega,
        Real.exp (lambda * X t omega) ∂P) =
        Real.exp ((t : Real) * (lambda ^ alpha)))
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L)
    (hKappa : ∀ (s q : NNReal),
      (∫ omega,
        Real.exp (-((q : Real) *
          (↑((inverseLocalTime L s omega).untopD 0) : Real))) ∂P) =
        Real.exp (-(s : Real) * kappa q)) :
    (∃ c : Real, 0 < c ∧
      ∀ q : NNReal, kappa q = c * ((q : Real) ^ (1 / alpha))) ∧
    (∀ t : NNReal, 0 < t →
      P {omega | 0 ≤ X t omega} =
        ENNReal.ofReal (1 / alpha)) ∧
    (∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega,
        Real.exp (-theta * runningMaximum X t omega) ∂P) =
        ∑' n : Nat,
          ((-theta * ((t : Real) ^ (1 / alpha))) ^ n) /
            Real.Gamma (1 + (n : Real) / alpha)) := by
  sorry

end Kyprianou.Ch06
