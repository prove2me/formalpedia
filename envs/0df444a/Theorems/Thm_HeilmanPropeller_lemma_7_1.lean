-- Prove2me | Theorems.Thm_HeilmanPropeller_lemma_7_1
-- name    : HeilmanPropeller.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:13.696072+00:00
-- url     : https://prove2.me/theorems/dfc973da-5b4a-4474-8bd3-9e7cbad49cde
-- title:
--   Lemma 7.1: an optimal partition has at most four cells
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $\mathcal A=(A_1,\dots,A_k)$ be a partition of $\mathbb R^{k-1}$ into measurable sets, each of positive measure, such that $F(\mathcal A)=C_k$. Then
--
--   $$k\le4.$$
--
--   With Lemma 2.1 this reduces the propeller problem to at most four cells in $\mathbb R^3$ (step (i) of the proof sketch, Section 1.1).
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: A achieves the supremum C_k (F(A) = C_k) → AchievesCk A: value A ≥ value B for every k-cell IsPartition B of every Space n; reason: a null modification changes no moment, so this is F(A) = C_k with C_k = value A; no real sSup is used
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 7.1, p.13

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanPropeller_AchievesCk

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller

/-- **Lemma 7.1 (the number of sets is at most four).** Heilman, *On the Propeller Conjecture*,
arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 7.1, p.13.

Let `(A₁, …, A_k) ⊆ ℝ^{k−1}` be a partition into measurable sets, each of positive measure, such that
`F(A) = C_k`. Then `k ≤ 4`.

**Formalization Note.** "Partition of measurable sets with `F(A) = C_k`" is `AchievesCk A`
(an `IsPartition`, a.e.-partition, of value at least that of every `k`-cell partition of every
`ℝⁿ`). -/
theorem lemma_7_1 (k : ℕ) (A : Fin k → Set (Space (k - 1))) (hA : AchievesCk A)
    (hpos : ∀ i, 0 < gaussian (k - 1) (A i)) : k ≤ 4 := by sorry

end HeilmanPropeller
