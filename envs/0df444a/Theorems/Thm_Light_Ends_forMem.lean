-- Prove2me | Theorems.Thm_Light_Ends_forMem
-- name    : Light.Ends.forMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:29:38.923052+00:00
-- url     : https://prove2.me/theorems/7683a7d0-743e-4ba9-b8a7-c9b20c49503c
-- title:
--   Ends: for Mem
-- statement:
--   **Counting loops whose body changes no local variable.**  Before round j the local variables are
--   the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
--   throughout, n fits in a word, and the body takes at most b steps.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L343-L363
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L343-L363

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round :
      ∀ (j : ℕ) (μ' : ℕ → ℤ),
        j < n →
          I j μ' →
            Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
              σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound :
      ∀ (j : ℕ) (μ' : ℕ → ℤ),
        j ≤ n → I j μ' → hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
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
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by sorry
