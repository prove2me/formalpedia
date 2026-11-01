-- Prove2me | Theorems.Thm_LowRankMEG_lemma_1
-- name    : LowRankMEG.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:45.552391+00:00
-- url     : https://prove2.me/theorems/d1a6ffa8-72a2-4385-b650-6ef878a584e8
-- title:
--   Lemma 1 — eigenvectors of $X^*$ are bottom eigenvectors of $\nabla f(X^*)$
-- statement:
--   Let $X^*\in\mathcal X^*$ be an optimal solution of Problem (1) with $\operatorname{rank}(X^*)=r^*$, and write $X^*=\sum_{i=1}^{r^*}\lambda_iv_iv_i^\top$. Then the $v_i$ are top eigenvectors of $-\nabla f(X^*)$: every eigenvector $v$ of $X^*$ with nonzero eigenvalue satisfies
--   $$
--   -\nabla f(X^*)\,v=\lambda_1(-\nabla f(X^*))\,v,\qquad \lambda_1(-\nabla f(X^*))=-\lambda_n(\nabla f(X^*)).
--   $$
--   So the rank of an optimal solution cannot exceed the multiplicity of the smallest eigenvalue of its gradient. The result is first-order optimality over the spectrahedron.
--
--   Differences from the source:
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
--   - encoding: λ_i with 1-based index → lam X i, with value 0 outside 1 ≤ i ≤ n; reason: every index used is in range under the hypotheses
--   - encoding: the set {v_i} of an eigen-decomposition of X* → every v with X* v = μ v, μ ≠ 0; reason: such a v is a combination of the v_i, and each v_i is such a v
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 1, p.3

import Mathlib
import Definitions.Def_LowRankMEG_Setting
import Definitions.Def_LowRankMEG_IsOptimal
import Definitions.Def_LowRankMEG_lam

namespace LowRankMEG

/-- **Lemma 1 (Lemma 7 in [15])**: for an optimal `X*`, every eigenvector of `X*` with a nonzero
eigenvalue is a top eigenvector of `−∇f(X*)`, for the eigenvalue `λ₁(−∇f(X*)) = −λ_n(∇f(X*))`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 1, p.3.

**Formalization Note.** "The set `{v_i}` of any eigen-decomposition `X* = ∑ λ_i v_i v_iᵀ`" is rendered
as every `v` with `X* v = μ v`, `μ ≠ 0`: such `v` is a combination of the `v_i`, and each `v_i` is such a `v`. -/
theorem lemma_1 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β)
    {Xs : Matrix (Fin n) (Fin n) ℝ} (hopt : IsOptimal f Xs)
    (v : Fin n → ℝ) (μ : ℝ) (hμ : μ ≠ 0) (hv : Xs.mulVec v = μ • v) :
    (-grad Xs).mulVec v = lam (-grad Xs) 1 • v ∧ lam (-grad Xs) 1 = -lam (grad Xs) n := by sorry

end LowRankMEG
