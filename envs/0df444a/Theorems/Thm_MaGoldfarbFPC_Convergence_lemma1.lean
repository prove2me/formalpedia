-- Prove2me | Theorems.Thm_MaGoldfarbFPC_Convergence_lemma1
-- name    : MaGoldfarbFPC.Convergence.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:10.469136+00:00
-- url     : https://prove2.me/theorems/615be002-9386-4cbd-9d87-ee5fa99a8c52
-- title:
--   Lemma 1 — the matrix shrinkage operator S_ν is nonexpansive in ‖·‖_F, with equality iff S_ν(Y₁) − S_ν(Y₂) = Y₁ − Y₂
-- statement:
--   Let $\nu>0$ and let $S_\nu$ be the matrix shrinkage operator on $\mathbb R^{m\times n}$: for a singular value decomposition $Y=U\,\mathrm{Diag}(\sigma)V^\top$, $S_\nu(Y)=U\,\mathrm{Diag}(\bar\sigma)V^\top$ with $\bar\sigma_i=\max(\sigma_i-\nu,0)$. For all $Y_1,Y_2\in\mathbb R^{m\times n}$,
--   $$\|S_\nu(Y_1)-S_\nu(Y_2)\|_F\le\|Y_1-Y_2\|_F \tag{3.1}$$
--   and
--   $$\|Y_1-Y_2\|_F=\|S_\nu(Y_1)-S_\nu(Y_2)\|_F\iff Y_1-Y_2=S_\nu(Y_1)-S_\nu(Y_2). \tag{3.2}$$
--
--   Non-expansiveness of the shrinkage, together with its equality case, is one of the two contraction-type properties on which the convergence of the fixed point iterations rests.
--
--   **Formalization Note** $S_\nu$ is the relation `IsShrink ν`: the lemma is stated for matrices $X_1,X_2$ with `IsShrink ν Y₁ X₁` and `IsShrink ν Y₂ X₂`, i.e. $X_i=S_\nu(Y_i)$ computed from some reduced SVD of $Y_i$. The two claims (3.1) and (3.2) form one conjunction.
-- source:
--   Ma, Goldfarb and Chen, Fixed point and Bregman iterative methods for matrix rank minimization, arXiv:0905.1643v2, p. 9, Lemma 1, (3.1)–(3.2)

import Mathlib
import Definitions.Def_MaGoldfarbFPC_Convergence_Basic

namespace MaGoldfarbFPC.Convergence

open CaiCandesShen.Convergence

/-- Lemma 1, p. 9: for `ν > 0` the matrix shrinkage operator `S_ν` is non-expansive in the
Frobenius norm, (3.1), and `‖Y₁ − Y₂‖_F = ‖S_ν(Y₁) − S_ν(Y₂)‖_F` holds if and only if
`Y₁ − Y₂ = S_ν(Y₁) − S_ν(Y₂)`, (3.2). Here `X₁ = S_ν(Y₁)` and `X₂ = S_ν(Y₂)`. -/
theorem lemma1 {m n : ℕ} (ν : ℝ) (hν : 0 < ν) (Y₁ Y₂ X₁ X₂ : Mat m n)
    (h₁ : IsShrink ν Y₁ X₁) (h₂ : IsShrink ν Y₂ X₂) :
    frobNorm (X₁ - X₂) ≤ frobNorm (Y₁ - Y₂) ∧
      (frobNorm (Y₁ - Y₂) = frobNorm (X₁ - X₂) ↔ Y₁ - Y₂ = X₁ - X₂) := by sorry

end MaGoldfarbFPC.Convergence
