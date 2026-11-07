-- Prove2me | Theorems.Thm_HeilmanPropeller_case_k2_bound
-- name    : HeilmanPropeller.case_k2_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:26.574615+00:00
-- url     : https://prove2.me/theorems/a49ab297-d656-48c6-89c4-debd0bf8c31d
-- title:
--   Two cells: $F(\mathcal A)\le 1/\pi$
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   For every $n$ and every partition $\mathcal A=(A_1,A_2)$ of $\mathbb R^n$ into two measurable sets,
--
--   $$\|z_1\|^2+\|z_2\|^2\le\frac1\pi\ \Big(<\frac{9}{8\pi}\Big).$$
--
--   This is the case $k=2$ of the proof of Theorem 1.1 and Remark 1.2 (citing Khot–Naor, Corollary 3.4; $C_2=1/\pi$, p.2). It rules out two-cell partitions in the equality case.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - generalization: the maximizing partition with two positive cells, in ℝ¹ after Lemma 2.1 → every two-cell IsPartition of every Space n; reason: C₂ = 1/π (p.2) is exactly this bound; it specializes to the proof's case
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), proof of Theorem 1.1 and Remark 1.2, case k = 2, p.7

import Mathlib
import Definitions.Def_GaussianPropeller

namespace HeilmanPropeller

open OAI.GaussianPropeller

/-- **Two cells: `F ≤ 1/π`.** Heilman, *On the Propeller Conjecture*, arXiv:2610.32158 (held
version, sha256 13f5ddf8…), proof of Theorem 1.1 and Remark 1.2, case `k = 2`, p.7 (citing
[KN08, Corollary 3.4]; also `C₂ = 1/π`, p.2).

For every `n` and every partition `A = (A₁, A₂)` of `ℝⁿ` into two sets,
`‖z₁‖² + ‖z₂‖² ≤ 1/π`.

**Formalization Note.** Stated for every two-cell `IsPartition` of every `ℝⁿ`, not only for the
maximizer with positive cells in `ℝ¹` that the proof reaches after Lemma 2.1. -/
theorem case_k2_bound (n : ℕ) (A : Fin 2 → Set (Space n)) (hA : IsPartition A) :
    value A ≤ 1 / Real.pi := by sorry

end HeilmanPropeller
