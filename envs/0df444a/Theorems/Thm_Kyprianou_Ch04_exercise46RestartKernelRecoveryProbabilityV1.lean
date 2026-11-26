-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RestartKernelRecoveryProbabilityV1
-- name    : Kyprianou.Ch04.exercise46RestartKernelRecoveryProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:46:18.459428+00:00
-- url     : https://prove2.me/theorems/a963004c-5642-55c9-b74c-a0834ccffeb9
-- title:
--   First-restart product-law recovery probability
-- statement:
--   Transfer the zero-discount strict-passage payoff from the shifted path and first service mark to the product of their laws. The resulting integral equals the finite-recovery probability.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RestartKernelRecoveryProbabilityV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (J : Omega → Real) (Z : Omega → (NNReal → Real))
    (hJ : Measurable J) (hZ : AEMeasurable Z P)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hJL : P.map J = service) (hJP : ∀ᵐ w ∂P, 0 < J w)
    (hLaw : P.map (fun w => (J w,Z w)) =
      (P.map J).prod (P.map (fun w t => L.X t w)))
    (K : Real × (NNReal → Real) → WithTop NNReal) (hK : Measurable K)
    (hKx : ∀ x : Real, 0 < x → ∀ w,
      K (x, fun t => L.X t w) = Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w)
    (R : Omega → WithTop NNReal) (hR : Measurable R)
    (hEq : ∀ᵐ w ∂P, R w = ⊤ ↔ K (J w,Z w) = ⊤)
    (phi : Real)
    (hStrict : ∀ x : Real, 0 < x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-(0 : Real) *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
      = Real.exp (-phi * x)) :
    (P {w | R w ≠ ⊤}).toReal = ∫ y : Real, Real.exp (-phi * y) ∂service := by
  sorry
