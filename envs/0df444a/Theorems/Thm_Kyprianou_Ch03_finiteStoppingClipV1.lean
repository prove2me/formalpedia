-- Prove2me | Theorems.Thm_Kyprianou_Ch03_finiteStoppingClipV1
-- name    : Kyprianou.Ch03.finiteStoppingClipV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:01:55.803807+00:00
-- url     : https://prove2.me/theorems/4b01cabd-bb6e-44ea-bc2c-7107aa27d28c
-- title:
--   Finite clipping of an extended stopping time preserves its value before the deterministic bound
-- statement:
--   Finite clipping of an extended stopping time preserves its value before the deterministic bound
-- source:
--   Kyprianou (2006), Exercise 3.2

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.finiteStoppingClipV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (r : Omega → NNReal)
    (hr : ∀ w, tau w ≠ ⊤ → tau w = (r w : WithTop NNReal))
    (s : NNReal) :
    ∃ rho : Omega → NNReal,
      IsStoppingTime F (fun w => (rho w : WithTop NNReal)) ∧
      (∀ w, rho w ≤ s) ∧
      (∀ w, tau w ≤ (s : WithTop NNReal) → rho w = r w) := by
  sorry
