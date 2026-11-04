-- Prove2me | Theorems.Thm_Light_Ends_forScratch
-- name    : Light.Ends.forScratch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:32:28.233357+00:00
-- url     : https://prove2.me/theorems/28602eb5-ae47-4c56-9932-d9f71b6b7e14
-- title:
--   Ends: for Scratch
-- statement:
--   **Counting loops whose body may change the scratch variables `xs`.**  Before round j the locals
--   are the given ones with j in the counter and anything in the scratch variables, and I j holds of the
--   memory.  The round says nothing about the locals.  The counter is not among the scratch variables,
--   so the body does not assign it.  The bound hi gives n, n fits in a word, and the body takes at most
--   b steps.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L349-L386
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L349-L386

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}

theorem Light.Ends.forScratch {i : ℕ} {hi : Expr} {body : Stmt} (xs : List ℕ) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ)
    (start : I 0 μ)
    (round :
      ∀ (j : ℕ) (loc' μ' : ℕ → ℤ),
        j < n →
          I j μ' → Ends lim P d body ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ b fun σ' => I (j + 1) σ'.mem)
    (done : ∀ loc' μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal (refreshLocals l loc' xs) i n), μ'⟩)
    (bound :
      ∀ (j : ℕ) (loc' μ' : ℕ → ℤ),
        j ≤ n → I j μ' → hi.Gives lim ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ n := by
      intros;
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hxs : body.assigns ⊆ xs := by simp) (hcounter : i ∉ xs := by simp) (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by
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
