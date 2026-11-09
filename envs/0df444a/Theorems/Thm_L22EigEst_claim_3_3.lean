-- Prove2me | Theorems.Thm_L22EigEst_claim_3_3
-- name    : L22EigEst.claim_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:20:28.463208+00:00
-- url     : https://prove2.me/theorems/e281f85b-95f0-4b86-ab70-21f4b050e265
-- title:
--   Claim 3.3 — $VAV^\top$ has the eigenvalues of $A$ plus $(s-1)n$ zeros
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be symmetric, $s\ge1$ an integer, and $V\in\mathbb R^{sn\times n}$ the matrix of Algorithm 2. Then the eigenvalues of $VAV^\top\in\mathbb R^{sn\times sn}$, counted with multiplicity, are those of $A$ together with $(s-1)n$ additional zeros:
--
--   $$\{\!\{\lambda(VAV^\top)\}\!\}=\{\!\{\lambda(A)\}\!\}+(s-1)n\cdot\{\!\{0\}\!\}.$$
--
--   In particular $VAV^\top$ has the same non-zero eigenvalues as $A$, so estimating the spectrum of $VAV^\top$ estimates that of $A$.
--
--   Differences from the source:
--   - generalization: "has the same non-zero eigenvalues as the matrix A" → the eigenvalue multiset of VAV⊺ equals that of A plus (s − 1)n zeros; reason: the conclusion of the claim's proof (p.12), used in the proof of Theorem 4; it implies the printed claim with multiplicities
--   - generalization: s = ⌈c log(1/ε)/ε²⌉ for ε ∈ (0, 1) → any integer s ≥ 1 (no ε); reason: the proof uses only that V has orthonormal columns, true for every s ≥ 1
--   - encoding: eigenvalues of VAV⊺ ∈ ℝ^{sn×sn} → Mathlib's eigenvalues on the index type Fin s × Fin n, compared as multisets; reason: the multiset does not depend on the order or the indexing
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Claim 3.3 and its proof, p.12

import Definitions.Def_L22EigEst_stackV

open Matrix

namespace L22EigEst

/-- **Claim 3.3** (p.12), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "Given a symmetric matrix A ∈ ℝ^{n×n} and accuracy parameter ε ∈ (0, 1), the matrix
VAV⊺ ∈ ℝ^{sn×sn} defined by Algorithm 2 has the same non-zero eigenvalues as the matrix A."
Stated in the form its proof concludes (p.12): "Hence the eigenvalues of VAV⊺ are those of A
together with (s − 1)n additional zeros."

**Formalization Note.** Eigenvalues are compared as multisets (with multiplicity), using Mathlib's
`IsHermitian.eigenvalues` on the index types `Fin s × Fin n` and `Fin n`; the multiset does not
depend on the order. Stated for every integer `s ≥ 1`. -/
theorem claim_3_3 (s n : ℕ) (hs : 1 ≤ s) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Finset.univ.val.map (stackV_conj_isHermitian s hA).eigenvalues =
      Finset.univ.val.map hA.eigenvalues + Multiset.replicate ((s - 1) * n) 0 := by sorry

end L22EigEst
