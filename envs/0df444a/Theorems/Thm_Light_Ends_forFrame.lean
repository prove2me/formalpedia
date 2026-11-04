-- Prove2me | Theorems.Thm_Light_Ends_forFrame
-- name    : Light.Ends.forFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:36.114006+00:00
-- url     : https://prove2.me/theorems/1ab8f7b8-bcde-41bf-8f75-42bfaa23893f
-- title:
--   Ends: for Frame
-- statement:
--   **Counting loops whose body is a block that changes no local variable**, with the locals as a
--   list.  Before round j the locals are the given ones with j in the counter, and I j holds of the
--   memory.  The bound hi gives n, and n fits in a word.  The round is a goal about the body, for the
--   rules of this file, and its time is body.blockCost, so that no number is typed.  A loop or a call
--   counts 0 steps in blockCost; for a body that contains one use Ends.forShape.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L155-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L155-L175

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}

theorem Light.Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ) (start : I 0 μ)
    (round :
      ∀ (j : ℕ) (μ' : ℕ → ℤ),
        j < n →
          I j μ' →
            Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
              σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' → hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by
      intros
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by
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
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by sorry
