-- Prove2me | Theorems.Thm_Light_Ends_pieceThen
-- name    : Light.Ends.pieceThen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:27:22.065975+00:00
-- url     : https://prove2.me/theorems/fef703a8-f6f6-4150-b591-1cda6fcf7144
-- title:
--   Ends: piece Then
-- statement:
--   A piece of the program about which `h` is known, followed by the rest of the program, which gets
--   the steps that are left.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L201-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L201-L204

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop} (h : Ends lim P d s₁ σ T₁ R)
    (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
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
    Ends lim P d (_root_.Light.Stmt.seq s₁ s₂) σ T Q := by sorry
