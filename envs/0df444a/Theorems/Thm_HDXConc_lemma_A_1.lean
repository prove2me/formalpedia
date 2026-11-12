-- Prove2me | Theorems.Thm_HDXConc_lemma_A_1
-- name    : HDXConc.lemma_A_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T15:58:06.202066+00:00
-- url     : https://prove2.me/theorems/81350866-9c32-4101-a276-c0dc10ea5cd1
-- title:
--   Lemma A.1, p.29 — Ostrowski's version of Sylvester's law of inertia
-- statement:
--   Let $A$ be a Hermitian matrix and $C$ a non-singular matrix of the same order $n$. Write $\lambda_1\ge\dots\ge\lambda_n$ for the eigenvalues in decreasing order. For every $j\in[n]$,
--
--   $$\lambda_j(C^*AC)=\theta_j\lambda_j(A)\quad\text{for some }\theta_j\text{ with }\lambda_{\min}(C^*C)\le\theta_j\le\lambda_{\max}(C^*C).$$
--
--   This quantifies how a congruence moves eigenvalues.
--
--   Differences from the source:
--   - generalization: Hermitian matrices, entries unspecified → matrices over any RCLike field; reason: this contains both the complex case and the real symmetric case the paper applies
--   - encoding: λ_j → Matrix.IsHermitian.eigenvalues₀ at the same index j on both sides, in decreasing order; reason: pairing the j-th largest eigenvalues is the same pairing as pairing the j-th smallest
--   - encoding: λ_min(C*C), λ_max(C*C) → ⨅ and ⨆ of eigenvalues₀ over Fin (card n); reason: the index set is finite and nonempty once a j exists, so these are the minimum and the maximum
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Lemma A.1, p.29; [Ost59, Theorem 1]

import Mathlib

open Matrix

namespace HDXConc

/-- Lemma A.1 (Ostrowski's version of Sylvester's law of inertia [Ost59, Theorem 1]), p.29: for a Hermitian
matrix `A` and a non-singular matrix `C` of the same order, for every `j`,
`λ_j(C* A C) = θ_j λ_j(A)` for some `θ_j` with `λ_min(C* C) ≤ θ_j ≤ λ_max(C* C)`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** `eigenvalues₀` lists the eigenvalues in decreasing order, and the same index `j` is used
on both sides. The infimum and supremum are over the finite index set `Fin (card n)`, which is nonempty once a
`j` exists, so they are the smallest and the largest eigenvalue of `C* C`. The statement is over any `RCLike`
field, which includes the real matrices of the paper's application and the complex ones. -/
theorem lemma_A_1 {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    (A C : Matrix n n 𝕜) (hA : A.IsHermitian) (hC : C.det ≠ 0) (j : Fin (Fintype.card n)) :
    ∃ θ : ℝ,
      ⨅ i, (isHermitian_conjTranspose_mul_self C).eigenvalues₀ i ≤ θ ∧
      θ ≤ ⨆ i, (isHermitian_conjTranspose_mul_self C).eigenvalues₀ i ∧
      (isHermitian_conjTranspose_mul_mul C hA).eigenvalues₀ j = θ * hA.eigenvalues₀ j := by sorry

end HDXConc
