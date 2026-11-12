-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_theorem_5
-- name    : IsingVectorBalancing.Subgaussian.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T01:34:00.969284+00:00
-- url     : https://prove2.me/theorems/e2b38291-974b-40cd-aa27-b6feb7f6f311
-- title:
--   Theorem 5 — discrete Alexandrov–Fenchel inequality
-- statement:
--   Let $C$ be a finite coordinate set and let $A\in\mathbb R^{C\times C}$ be Lorentzian: symmetric, entrywise nonnegative, with at most one positive eigenvalue counted with multiplicity. For any integer $k\ge2$, let $x_1\in\mathbb R^C$ be arbitrary and let $x_2,\ldots,x_k\in\mathbb R^C_{\ge0}$. With
--   $$V_A(x_1,\ldots,x_k)=\sum_{c:[k]\to C}\prod_i x_i(c(i))\prod_{i<j}A(c(i),c(j)),$$
--   one has
--   $$V_A(x_1,x_2,x_3,\ldots,x_k)^2\ge
--   V_A(x_1,x_1,x_3,\ldots,x_k)V_A(x_2,x_2,x_3,\ldots,x_k).$$
--   All assignments, including repeated coordinates, contribute to this sum. The first selection may have negative coordinates, and all other selections may have zeros. The statement retains the zero matrix and singular matrices. It provides the discrete polynomial inequality needed for the covariance estimate.
--
--   Differences from the source:
--   - encoding: k selections with k at least 2 → two leading selections and a tail indexed by Fin m, with k = m + 2; reason: every arity k at least 2 has a unique such tail length, avoiding truncated indexing
--   - encoding: symmetric Lorentzian matrices and unordered pairs → real Hermitian spectral predicate and ordered indices i < j; reason: real symmetry and eigenvalue multiplicity are preserved and each unordered pair occurs once
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, p. 5 (PDF 6), Theorem 5, Eq. (4), with Eq. (3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz

set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

/-- k = m + 2 covers every k ≥ 2 without truncated indexing. -/
theorem theorem_5 {C : Type*} [Fintype C] [DecidableEq C] (m : ℕ)
    (A : Matrix C C ℝ) (hA : IsLorentzian A)
    (x₁ x₂ : C → ℝ) (tail : Fin m → C → ℝ)
    (hx₂ : ∀ c, 0 ≤ x₂ c) (htail : ∀ i c, 0 ≤ tail i c) :
    selectionPolynomial A (selections x₁ x₂ tail) ^ 2 ≥
      selectionPolynomial A (selections x₁ x₁ tail) *
      selectionPolynomial A (selections x₂ x₂ tail) := by sorry

end IsingVectorBalancing.Subgaussian
