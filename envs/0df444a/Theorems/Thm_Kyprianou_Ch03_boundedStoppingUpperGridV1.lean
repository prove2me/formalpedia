-- Prove2me | Theorems.Thm_Kyprianou_Ch03_boundedStoppingUpperGridV1
-- name    : Kyprianou.Ch03.boundedStoppingUpperGridV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T15:13:23.687559+00:00
-- url     : https://prove2.me/theorems/87138f38-2362-4ceb-9c8e-d412be1bb001
-- title:
--   Upper grid approximation of bounded stopping times
-- statement:
--   A bounded finite stopping time has countable-range upper approximations in its original filtration, capped at the same horizon.
-- source:
--   Kyprianou (2006), Corollary 3.11; faithful support for e939e617-26cc-4e11-98c6-e87492aefbb3

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.boundedStoppingUpperGridV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (rho : Omega → NNReal)
    (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal)))
    (n : NNReal) (hBound : ∀ w, rho w ≤ n)
    : ∃ (G : ℕ → Omega → NNReal),
      (∀ k, IsStoppingTime F (fun w => (G k w : WithTop NNReal))) ∧
      (∀ k, (Set.range (fun w => (G k w : WithTop NNReal))).Countable) ∧
      (∀ k w, rho w ≤ G k w) ∧ (∀ k w, G k w ≤ n) ∧
      (∀ w, Tendsto (fun k => G k w) atTop (nhds (rho w))) := by sorry
