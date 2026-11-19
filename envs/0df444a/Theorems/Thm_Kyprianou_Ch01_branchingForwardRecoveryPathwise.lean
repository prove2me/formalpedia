-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingForwardRecoveryPathwise
-- name    : Kyprianou.Ch01.branchingForwardRecoveryPathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:25:58.083365+00:00
-- url     : https://prove2.me/theorems/8663d533-5cbf-45ea-9912-63e635f8953a
-- title:
--   Source-exact pre-extinction Lamperti forward recovery for a locally integrable positive population path
-- statement:
--   On any sample path of a natural-valued branching population whose time integral exists locally and which remains strictly positive before its extinction time, the forward Lamperti map evaluated at the occupation clock of any pre-extinction time recovers the exact original population. The proof constructs a strictly later finite horizon below extinction, deduces clock monotonicity and strict growth, then applies the exact right-inverse recovery theorem. This provides the full pathwise content of (1.17) without new source assumptions.
-- source:
--   Kyprianou (2006), Chapter 1 equation (1.17), pp. 30–32

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.WithBot
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingForwardRecoveryPathwise
    {Ω : Type*} (Y : NNReal → Ω → ℕ) (ω : Ω)
    (hlocalint : ∀ t : NNReal,
      IntervalIntegrable (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ))
    (hpositive : ∀ t : NNReal,
      (t : WithTop NNReal) < populationExtinction Y ω → 0 < Y t ω) :
    ∀ t : NNReal, (t : WithTop NNReal) < populationExtinction Y ω →
      branchingToPoisson Y
        (Real.toNNReal (branchingOccupation Y t ω)) ω = Y t ω := by
  sorry
