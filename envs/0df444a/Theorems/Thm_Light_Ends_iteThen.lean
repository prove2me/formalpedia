-- Prove2me | Theorems.Thm_Light_Ends_iteThen
-- name    : Light.Ends.iteThen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:28:59.70949+00:00
-- url     : https://prove2.me/theorems/4f78644b-982a-4dce-a453-5a7e5fa949ef
-- title:
--   Ends: ite Then
-- statement:
--   A branch, followed by the rest of the program: each side, with the rest of the program behind
--   it, gets the steps that the test leaves.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L252-L263
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L252-L263

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d (_root_.Light.Stmt.seq s₁ s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬c.Holds σ → Ends lim P d (_root_.Light.Stmt.seq s₂ s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hT : c.cost + 1 ≤ T := by
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
    Ends lim P d (_root_.Light.Stmt.seq (.ite c s₁ s₂) s) σ T Q := by sorry
