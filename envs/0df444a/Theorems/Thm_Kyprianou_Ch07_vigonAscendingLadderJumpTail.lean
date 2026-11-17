-- Prove2me | Theorems.Thm_Kyprianou_Ch07_vigonAscendingLadderJumpTail
-- name    : Kyprianou.Ch07.vigonAscendingLadderJumpTail
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:55:40.028907+00:00
-- url     : https://prove2.me/theorems/37f14818-1e25-471a-93e0-f7c2547014f7
-- title:
--   Theorem 7.8: Vigon identity for ascending ladder-height jump tails
-- statement:
--   For a non-compound-Poisson real Lévy process X, take the actual ascending and descending ladder heights from admissible local times at the supremum and infimum. Tie the ascending ladder-height jump measure Π_H to its actual killed-subordinator Laplace exponent, the descending potential U-hat to the original descending ladder process, and the two local-time normalisations by the Wiener–Hopf factorisation with multiplicative constant one. Theorem 7.8 states for every y>0 that Π_H(y,∞)=∫_[0,∞) U-hat(dz)Π(y+z,∞). The original jump measure Π is the one in the genuine Lévy–Khintchine characteristic exponent of X, not an independent measure. The Wiener–Hopf factors at imaginary arguments are required to be the true characteristic exponents of the original ascending and descending ladder-height processes, fixing their relative local-time normalisation.
-- source:
--   Kyprianou (2006), Theorem 7.8, printed p.195, original single-page PDF p.204, Windows Ky.pdf sheet 103.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.8 (Vigon): the jump tail of the actual ascending
ladder height equals the original Lévy jump tail integrated against
the potential of the descending ladder height. -/
theorem vigonAscendingLadderJumpTail
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup Ldown : NNReal → Omega → NNReal)
    (b : Real) (sigma2 : NNReal)
    (Pi PiH Uhat : Measure Real)
    (etaUp driftUp : Real) (phiUp : Real → Real)
    (Psi : Real → Complex)
    (kappaUp kappaDown : Complex → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hXTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet
      P X b sigma2 Pi)
    (hLocalUp : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F X Lup)
    (hLocalDown : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F (fun t omega => -X t omega) Ldown)
    (hHTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet
      etaUp driftUp PiH phiUp)
    (hAscendingLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Lup t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-theta *
          Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega) ∂P) =
      Real.exp (-(t : Real) * phiUp theta))
    (hAscendingExponent : ∀ theta : Real, 0 ≤ theta →
      kappaUp (theta : Complex) = (phiUp theta : Complex))
    (hDescendingLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Ldown t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-theta *
          Kyprianou.Ch06.runningMaximum (fun s w => -X s w)
            (tau.untopD 0) omega) ∂P) =
      Real.exp (-(t : Real) *
        (kappaDown (theta : Complex)).re))
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta))
    (hUpCharacteristic : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Lup t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp
          (Complex.I * (theta : Complex) *
            (↑(Kyprianou.Ch06.runningMaximum X
              (tau.untopD 0) omega) : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) *
          kappaUp (-(Complex.I * (theta : Complex)))))
    (hDownCharacteristic : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Ldown t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp
          (-(Complex.I * (theta : Complex)) *
            (↑(Kyprianou.Ch06.runningMaximum
              (fun s w => -X s w) (tau.untopD 0) omega) : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) *
          kappaDown (Complex.I * (theta : Complex))))
    (hWienerHopfNormalization : ∀ theta : Real,
      kappaUp (-(Complex.I * (theta : Complex))) *
        kappaDown (Complex.I * (theta : Complex)) = Psi theta)
    (hDescendingPotential : ∀ B : Set Real, MeasurableSet B →
      Uhat B =
        ∫⁻ t : Real in Set.Ici 0,
          P {omega | let tau :=
              Kyprianou.Ch06.inverseLocalTime Ldown (Real.toNNReal t) omega
            tau ≠ ⊤ ∧
              Kyprianou.Ch06.runningMaximum
                (fun s w => -X s w) (tau.untopD 0) omega ∈ B}
          ∂volume) :
    ∀ y : Real, 0 < y →
      PiH (Set.Ioi y) =
        ∫⁻ z : Real in Set.Ici 0,
          Pi (Set.Ioi (y + z)) ∂Uhat := by
  sorry

end Kyprianou.Ch07
