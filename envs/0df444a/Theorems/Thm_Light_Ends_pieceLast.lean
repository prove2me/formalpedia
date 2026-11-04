-- Prove2me | Theorems.Thm_Light_Ends_pieceLast
-- name    : Light.Ends.pieceLast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:27:50.944758+00:00
-- url     : https://prove2.me/theorems/9015f917-a1bb-42b0-9f65-1576f49b6e79
-- title:
--   Ends: piece Last
-- statement:
--   A piece of the program about which `h` is known, at the end of the program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L207-L210
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L207-L210

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop} (h : Ends lim P d s σ T₁ R)
    (rest : ∀ σ', R σ' → Q σ')
    (hT : T₁ ≤ T := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))) :
    Ends lim P d s σ T Q := by sorry
