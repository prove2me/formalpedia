-- Prove2me | Theorems.Thm_Light_Ends_setValThen
-- name    : Light.Ends.setValThen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:30:25.364651+00:00
-- url     : https://prove2.me/theorems/24909eaf-b6bd-4831-a879-a2621ed0c043
-- title:
--   Ends: set Val Then
-- statement:
--   `x := e ; s`, where e gives z, for locals that are not given as a list.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L104-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L104-L108

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_Ends_set
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}

theorem Light.Ends.setValThen {loc : ℕ → ℤ} {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨Function.update loc x z, μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨loc, μ⟩ z := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hT : e.cost + 1 ≤ T := by
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
    Ends lim P d (_root_.Light.Stmt.seq (.set x e) s) ⟨loc, μ⟩ T Q := by sorry
