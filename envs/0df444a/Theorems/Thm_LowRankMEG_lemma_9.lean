-- Prove2me | Theorems.Thm_LowRankMEG_lemma_9
-- name    : LowRankMEG.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:34.253354+00:00
-- url     : https://prove2.me/theorems/97693168-0db9-4570-8880-c878cd881af8
-- title:
--   Lemma 9 — a Davis–Kahan bound for projectors
-- statement:
--   Let $X\in\mathcal S_n$ have rank $r$ and eigen-decomposition $X=V_r\Lambda_rV_r^\top$ with $V_r\in\mathbb R^{n\times r}$. Let $Z$ be symmetric, and let $W_r\in\mathbb R^{n\times r}$ have as columns the $r$ leading eigenvectors of $Z$. Then
--   $$
--   \|W_rW_r^\top-V_rV_r^\top\|_F\le\frac{2\|Z-X\|_F}{\lambda_r(X)}.
--   $$
--   It compares the leading eigenspace of a nearby matrix with that of a low-rank one, with no rotation and no assumption on the gap of $Z$. It gives the step (a) of (25).
--
--   Differences from the source:
--   - generalization: Z ∈ 𝒮_n → Z any symmetric matrix; reason: 𝒮_n consists of symmetric matrices, and the proof on p.42 uses only symmetry of Z
--   - encoding: W_r, the r leading eigenvectors of Z → any W with WᵀW = 1 and Z W = W diag(λ_1(Z), …, λ_r(Z)); reason: every valid choice is covered at a tie
--   - encoding: X = V_r Λ_r V_rᵀ → IsCompactEigen X V Λ, with Λ positive; reason: X ⪰ 0 has rank r, so its nonzero eigenvalues are positive
--   - encoding: λ_i with 1-based index → lam X i, with value 0 outside 1 ≤ i ≤ n; reason: every index used is in range under the hypotheses
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 9, p.41

import Mathlib
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_LowRankMEG_IsCompactEigen

namespace LowRankMEG

/-- **Lemma 9, a variant of Davis–Kahan**: for `X ∈ 𝒮_n` of rank `r` with `X = V_r Λ_r V_rᵀ`, and `W_r` the `r`
leading eigenvectors of `Z`: `‖W_r W_rᵀ − V_r V_rᵀ‖_F ≤ 2‖Z − X‖_F / λ_r(X)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 9, p.41.

**Formalization Note.** `Z` is any symmetric matrix; the page has `Z ∈ 𝒮_n`, a special case. `W` is any
`n × r` matrix with orthonormal columns that are eigenvectors of `Z` for `λ_1(Z), …, λ_r(Z)`. -/
theorem lemma_9 {n : ℕ} {X Z : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hZ : Z.IsSymm)
    {V W : Matrix (Fin n) (Fin X.rank) ℝ} {Λ : Fin X.rank → ℝ}
    (hdec : IsCompactEigen X V Λ)
    (hW : W.transpose * W = 1)
    (hWe : Z * W = W * Matrix.diagonal (fun i : Fin X.rank => lam Z ((i : ℕ) + 1))) :
    frobNorm (W * W.transpose - V * V.transpose) ≤ 2 * frobNorm (Z - X) / lam X X.rank := by sorry

end LowRankMEG
