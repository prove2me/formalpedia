-- Prove2me | Theorems.Thm_LLLFactor_Reduction_situation_initial_final
-- name    : LLLFactor.Reduction.situation_initial_final
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:27.392204+00:00
-- url     : https://prove2.me/theorems/e6928cc3-7d9e-44bf-b277-be87ce4c0a3f
-- title:
--   (1.15), p. 519 — (1.16)–(1.17) hold trivially at k = 2, and at k = n + 1 they say the basis is reduced
-- statement:
--   Let $b_1,\dots,b_n\in\mathbb R^n$. Write $\mathrm{Sit}(b,k)$ for the situation of (1.15) at subscript $k$:
--   $$\text{(1.16)}\ |\mu_{ij}|\le\tfrac12\ \ (1\le j<i<k),\qquad \text{(1.17)}\ |b_i^*+\mu_{i,i-1}b_{i-1}^*|^2\ge\tfrac34|b_{i-1}^*|^2\ \ (1<i<k).$$
--   Then:
--
--   1. $\mathrm{Sit}(b,2)$ holds for every $b$ ("these conditions are trivially satisfied if $k=2$");
--   2. if $\mathrm{Sit}(b,n+1)$ holds, then $b$ satisfies (1.4) and (1.5), i.e. the basis is reduced ("if $k=n+1$ then the basis is reduced").
--
--   Together with the invariance of the situation under a step, this shows that the algorithm, when it stops, has produced a reduced basis.
--
--   **Formalization Note.** The indices are 0-based in Lean; (1.16) is stated for Lean indices $j<i$ with $i+1<k$, and (1.17) for the paper's $i$ with $2\le i<k$, $i\le n$.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 519, (1.15)–(1.17)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem situation_initial_final {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) :
    Situation b 2 ∧ (Situation b (n + 1) → LLLFactor.RedBasis.IsReduced b) := by sorry

end LLLFactor.Reduction
