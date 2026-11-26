-- Prove2me | Theorems.Thm_Kyprianou_Ch04_limitingDrawdownTransformAndDrift
-- name    : Kyprianou.Ch04.limitingDrawdownTransformAndDrift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T22:25:44.51811+00:00
-- url     : https://prove2.me/theorems/e79ddc43-3efd-445f-be2f-d65b8debd3ba
-- title:
--   Corollary 4.9: limiting running-supremum drawdown transform and drift classification
-- statement:
--   The limiting Laplace transform of the running-supremum drawdown barX_t - X_t as t→∞ equals (max(0,psi'(0+))*beta)/psi(beta) for beta>0. The all-time infimum of the spectrally negative Levy process is -infinity almost surely precisely when psi'(0+)≤0, and finite almost surely when psi'(0+)>0. The time-dependent drawdown is not assumed to converge almost surely; the transform converges and corresponds in law to the negative all-time infimum through Levy time-reversal duality. The nonpositive-mean condition is defined directly by arbitrarily small positive secant slopes, covering the possibility that psi'(0+)=-infinity; the nonnegative slope coefficient comes from the infimum of positive secant slopes.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.9, printed page 100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Corollary 4.9 (p. 100): limiting transform of running supremum minus X, and drift classification. -/
theorem limitingDrawdownTransformAndDrift
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))) :
    let nonnegativeSlope : Real :=
      max 0 (sInf ((fun theta : Real => L.ψ theta / theta) '' Set.Ioi 0))
    let meanNonpositive : Prop :=
      forall epsilon : Real, 0 < epsilon ->
        exists theta : Real, 0 < theta ∧ L.ψ theta < epsilon * theta
    (∀ beta : Real, 0 < beta →
      Tendsto
        (fun t : NNReal =>
          ∫ omega, Real.exp (-beta *
            (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t) - L.X t omega)) ∂P)
        atTop (nhds (nonnegativeSlope * beta / L.ψ beta))) ∧
    (meanNonpositive ↔
      (P {omega : Omega |
        ¬ BddBelow (Set.range
          (fun t : NNReal => L.X t omega))}).toReal = 1) ∧
    (¬ meanNonpositive →
      (P {omega : Omega |
        BddBelow (Set.range
          (fun t : NNReal => L.X t omega))}).toReal = 1) := by
  sorry
end Kyprianou.Ch04
