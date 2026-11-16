-- Prove2me | Theorems.Thm_Kyprianou_Ch06_secondWienerHopfFactorisationIdentity
-- name    : Kyprianou.Ch06.secondWienerHopfFactorisationIdentity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:13:26.563175+00:00
-- url     : https://prove2.me/theorems/a9e6b998-868e-431f-99eb-dd939c3d36c7
-- title:
--   Exercise 6.7: both second factorisation identities
-- statement:
--   For a non-subordinator real Lévy process and its first strict upward passage time, prove both parts of Exercise 6.7. First, for every real barrier x, α>0 and β≥0, identify the discounted first-passage transform as the ratio of the exponential-time running-supremum tail transform to the unrestricted supremum transform. Second, for α>0, β≥0 and q>0 with κ(α,q)≠0, identify the Laplace-in-barrier overshoot transform with the divided difference [κ(α,q)−κ(α,β)]/[(q−β)κ(α,q)] when q≠β. At q=β, the statement also requires differentiability of u↦κ(α,u) at β as a conclusion and identifies the transform with κ'_β(α,β)/κ(α,β). Thus the removable diagonal is included in the formal theorem and does not enter as an assumption.
-- source:
--   Kyprianou (2006), Exercise 6.7(i)–(ii), printed pp. 176–177; physical PDF pp. 93–94.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.7: the second Wiener-Hopf factorisation. Its first part
is the exact one-sided first-passage identity at every x in R. Its
second part is the Laplace-in-barrier transform of the discounted
overshoot for q>0, including the removable diagonal q=beta. At
q=beta, differentiability and the derivative quotient are asserted
as conclusions rather than assumed. -/
theorem secondWienerHopfFactorisationIdentity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (F : NNReal → MeasurableSpace Omega)
    (expTime : Real → Omega → NNReal)
    (kappa : Real → Real → Real)
    (hX : IsRealLevyProcess P X)
    (hNotSubordinator : ¬ IsSubordinatorProcess P X)
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L)
    (hExpTime : ∀ (alpha : Real), 0 < alpha →
      ∀ t : NNReal,
        P {omega | t < expTime alpha omega} =
          ENNReal.ofReal (Real.exp (-alpha * (t : Real))))
    (hExpIndependent : ∀ alpha : Real, 0 < alpha →
      ∀ (m : Nat) (times : Fin m → NNReal)
        (A : Fin m → Set Real) (B : Set NNReal),
        (∀ i, MeasurableSet (A i)) → MeasurableSet B →
        P {omega | expTime alpha omega ∈ B ∧
          (∀ i : Fin m, X (times i) omega ∈ A i)} =
            P {omega | expTime alpha omega ∈ B} *
            P {omega |
              ∀ i : Fin m, X (times i) omega ∈ A i})
    (hKappa : ∀ (alpha beta : Real), 0 ≤ alpha → 0 ≤ beta →
      ∀ t : NNReal,
        (∫ omega,
          let tau := inverseLocalTime L t omega
          if tau = ⊤ then (0 : Real)
          else Real.exp (-alpha * (↑(tau.untopD 0) : Real) -
            beta * runningMaximum X (tau.untopD 0) omega) ∂P) =
        Real.exp (-(t : Real) * kappa alpha beta)) :
    (∀ (alpha beta x : Real), 0 < alpha → 0 ≤ beta →
      (∫ omega,
        let tau := firstEntranceTime X 0 (Set.Ioi x) omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-alpha * (↑(tau.untopD 0) : Real) -
          beta * X (tau.untopD 0) omega) ∂P) =
      (∫ omega,
        if x < runningMaximum X (expTime alpha omega) omega
        then Real.exp (-beta *
          runningMaximum X (expTime alpha omega) omega)
        else (0 : Real) ∂P) /
      (∫ omega,
        Real.exp (-beta *
          runningMaximum X (expTime alpha omega) omega) ∂P)) ∧
    (∀ (alpha beta q : Real),
      0 < alpha → 0 ≤ beta → 0 < q →
      kappa alpha q ≠ 0 →
      (q = beta →
        DifferentiableAt Real (fun u => kappa alpha u) beta) ∧
      (∫ x in Set.Ioi (0 : Real),
        Real.exp (-q * x) *
          (∫ omega,
            let tau := firstEntranceTime X 0 (Set.Ioi x) omega
            if tau = ⊤ then (0 : Real)
            else Real.exp (-alpha * (↑(tau.untopD 0) : Real) -
              beta * (X (tau.untopD 0) omega - x)) ∂P) ∂volume) =
      (if q = beta then
        deriv (fun u => kappa alpha u) beta /
          kappa alpha beta
      else
        (kappa alpha q - kappa alpha beta) /
          ((q - beta) * kappa alpha q))) := by
  sorry

end Kyprianou.Ch06
