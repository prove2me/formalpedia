-- Prove2me | Theorems.Thm_GridHam_unitStepChain_intermediate
-- name    : GridHam.unitStepChain_intermediate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:49:39.16028+00:00
-- url     : https://prove2.me/theorems/084a487c-6066-4db5-a38d-3e797e2ca2be
-- title:
--   Grid Ham: unit Step Chain intermediate
-- statement:
--   **Discrete intermediate value property for unit-step chains.** If `x`
--   and `y` both appear in a unit-step chain `q`, every value between them also
--   appears -- regardless of `Nodup`; this is purely about connectivity of the
--   ±1-step walk (to get from `x` to `y` via ±1 steps, you must pass through
--   every integer in between). This is the crux fact behind
--   `unitChain_endpoints`: an interior starting point `a` (with both `a-1` and
--   `a+1` present elsewhere, by full coverage of the range) would force the
--   walk to pass back through `a` to reach the far one -- contradicting
--   `Nodup`, since `a` is only visited once, at the start.
--
--   Proved by front-peeling induction, mirroring the exact structure already
--   confirmed working in `Coloring.lean`'s `chain_parity_alternates` (unfold
--   `unitStepChain` via `simpa [unitStepChain]`, split the `&&` via `simp`,
--   recover the underlying `Prop` from the `decide`-wrapped `Bool` via
--   `unfold ... ; by_contra ; simp [...]`).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L52-L102
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L52-L102

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.unitStepChain_intermediate :
    ∀ (q : List ℕ), unitStepChain q = true →
      ∀ x y, x ∈ q → y ∈ q →
        ∀ z, (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x) → z ∈ q := by sorry
