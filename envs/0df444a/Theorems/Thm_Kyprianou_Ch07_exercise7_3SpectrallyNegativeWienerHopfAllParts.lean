-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_3SpectrallyNegativeWienerHopfAllParts
-- name    : Kyprianou.Ch07.exercise7_3SpectrallyNegativeWienerHopfAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T15:02:07.037042+00:00
-- url     : https://prove2.me/theorems/7a657ef2-186f-41ac-a1f0-9e61fc7c5431
-- title:
--   Exercise 7.3: both Wiener–Hopf extremal transforms and drift trichotomy
-- statement:
--   Exercise 7.3 has four full parts for a nonmonotone spectrally negative Lévy process X with Laplace exponent ψ, right inverse Φ and finite derivative ψ'(0)=E X₁. (i) Show the all-time infimum transform E[e^{β underbar X_∞}1_{underbar X_∞>−∞}] equals zero if ψ'(0)<0 and ψ'(0)β/ψ(β) if ψ'(0)≥0. (ii) Show the all-time supremum transform E[e^{−β bar X_∞}1_{bar X_∞<∞}] equals Φ(0)/(β+Φ(0)) if ψ'(0)<0 and zero otherwise. (iii) Derive drift to +∞, drift to −∞, or path oscillation according to the sign of E X₁. (iv) A spectrally negative α-stable process with α∈(1,2) necessarily oscillates. Finite supremum and infimum indicators are represented explicitly to avoid treating infinity as a real number. The right derivative psi'(0+) is now a WithBot Real limit, admitting -infinity; finite nonnegative derivatives retain the beta psi(beta) transform coefficient. Only negative subordinators are excluded to ensure the textbook right-inverse/maximum formula; positive deterministic drift is retained.
-- source:
--   Kyprianou (2006), Exercise 7.3(i)–(iv), printed p.207, original PDF p.216, Windows Ky.pdf sheet 109.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.3(i)-(iv): both all-time Wiener-Hopf factors,
the mean-driven drift/oscillation trichotomy and the stable case. -/
theorem exercise7_3SpectrallyNegativeWienerHopfAllParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (psi : Real → Real) (Phi0 : Real) (drift : WithBot Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hSpectralNegative : Pi (Set.Ioi 0) = 0)
    (hNotNegativeSubordinator :
      ¬ ∀ᵐ omega ∂P, Monotone (fun t : NNReal => -X t omega))
    (hLaplace : ∀ theta : Real, 0 ≤ theta →
       (∫ omega, Real.exp (theta * X 1 omega) ∂P) =
         Real.exp (psi theta))
    (hPsi0 : psi 0 = 0)
    (hDerivative : Tendsto
      (fun theta : Real =>
        (((psi theta - psi 0) / theta : Real) : WithBot Real))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds drift))
    (hPhi : 0 ≤ Phi0 ∧ psi Phi0 = 0 ∧
       ∀ theta : Real, 0 ≤ theta → psi theta = 0 → theta ≤ Phi0) :
    let infFinite : Omega → Prop := fun omega =>
      ∃ M : Real, ∀ t : NNReal, -M ≤ X t omega
    let supFinite : Omega → Prop := fun omega =>
      ∃ M : Real, ∀ t : NNReal, X t omega ≤ M
    let infimum : Omega → Real := fun omega =>
      sInf {x : Real | ∃ t : NNReal, x = X t omega}
    let supremum : Omega → Real := fun omega =>
      sSup {x : Real | ∃ t : NNReal, x = X t omega}
    ((∀ beta : Real, 0 < beta →
       ((drift < 0 →
          (∫ omega, if infFinite omega
            then Real.exp (beta * infimum omega) else 0 ∂P) = 0) ∧
        (∀ d : Real, drift = (d : WithBot Real) → 0 ≤ d →
          (∫ omega, if infFinite omega
            then Real.exp (beta * infimum omega) else 0 ∂P) =
               d * beta / psi beta))) ∧
     (∀ beta : Real, 0 < beta →
       ((drift < 0 →
         (∫ omega, if supFinite omega
           then Real.exp (-beta * supremum omega) else 0 ∂P) =
           Phi0 / (beta + Phi0)) ∧
        ((0 : WithBot Real) ≤ drift →
         (∫ omega, if supFinite omega
           then Real.exp (-beta * supremum omega) else 0 ∂P) = 0))) ∧
     ((0 : WithBot Real) < drift → DriftsToPosInfinity P X) ∧
     (drift < 0 → DriftsToNegInfinity P X) ∧
     (drift = (0 : WithBot Real) → OscillatesAtInfinity P X) ∧
     (∀ alpha c : Real, 1 < alpha → alpha < 2 → 0 < c →
       (∀ theta : Real, 0 ≤ theta → psi theta = c * theta ^ alpha) →
       OscillatesAtInfinity P X)) := by
  sorry

end Kyprianou.Ch07
