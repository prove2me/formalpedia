-- Prove2me | Theorems.Thm_Lean4LPD_layer_cumulation
-- name    : Lean4LPD.layer_cumulation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:06:22.458822+00:00
-- url     : https://prove2.me/theorems/d5176141-3a94-4faf-9e41-9220e68c4d71
-- title:
--   Lean4 LPD: layer cumulation
-- statement:
--   **Per-layer high-weight cumulation.** Formalizes part (ii) of
--   `apd:cor:norm_cumulation_jump`, the bound `apd:eq:layer_cumulation`:
--
--     `N_{≥m}^{(T)} ≤ C(T, m) · sin^m(dt) · (∏_{j=2}^{m+1} w_j) · ‖O‖`,
--
--   for a ladder whose per-layer coefficient is the single-jump layer inflow `w_{m+1} · sin(dt)`
--   (the `j = 1` case of `apd:thm:layer_inflow`).
--
--   This counts **single-jump inflow only**, which is the scope of `apd:eq:layer_cumulation`. The
--   multi-jump and overshoot sectors are additive, not multiplicative — a single layer can already
--   truncate mass while `C(T,m)` is still zero — and are handled by the first-passage majorant of
--   `apd:rmk:multijump` (`MultiLadder.le_majorant`), not here.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L167-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L167-L173

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.layer_cumulation {M a : ℝ} {w : ℕ → ℝ} (ha : 0 ≤ a) (hw : ∀ j, 0 ≤ w j)
    (L : WeightedLadder (fun m => w (m + 1) * a) M) (m g : ℕ) :
    L.N m g ≤ (g.choose m : ℝ) * a ^ m * (∏ j ∈ Finset.Icc 2 (m + 1), w j) * M := by sorry
