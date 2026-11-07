-- Prove2me | Theorems.Thm_HeilmanPropeller_case_k4_strict
-- name    : HeilmanPropeller.case_k4_strict
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:33.1252+00:00
-- url     : https://prove2.me/theorems/d046bb25-8e4e-4ab0-a82c-c1e9d49f3257
-- title:
--   Four cells in $\mathbb R^3$: critical partitions have $F<9/(8\pi)$
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $\mathcal A=(A_1,\dots,A_4)$ be a partition of $\mathbb R^3$ with $\gamma_3(A_i)>0$ for all $i$, satisfying the critical point condition (2.2) with $\operatorname{span}(z_1,\dots,z_4)$ of dimension $3$ (the partitions classified by Lemma 3.1). Then
--
--   $$\sum_{i=1}^4\|z_i\|^2<\frac{9}{8\pi}.$$
--
--   This is the case $k=4$ of the proof of Theorem 1.1 and Remark 1.2: Lemma 3.1 leaves two candidate partitions, and an explicit calculation (Heilman–Jagannath–Naor, Lemma 4.1) shows both are strictly below $9/(8\pi)$. It rules out four-cell partitions in the equality case.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - reading: "there are only two different partitions that could maximize F(A) (up to symmetries), and … they satisfy Σ‖zᵢ‖² < 9/(8π)" → the strict bound for every partition satisfying Lemma 3.1's hypotheses; reason: "they" are the two critical partitions of Lemma 3.1; a maximizer with four positive cells in ℝ³ is one of them
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), proof of Theorem 1.1 and Remark 1.2, case k = 4, p.7

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller
open OAI.GaussianPropeller.Reduction (closedCell)

/-- **Four cells in `ℝ³`: the critical partitions are strictly below `9/(8π)`.** Heilman, *On the
Propeller Conjecture*, arXiv:2610.32158 (held version, sha256 13f5ddf8…), proof of Theorem 1.1 and
Remark 1.2, case `k = 4`, p.7 (citing Lemma 3.1 and [HJN13, Lemma 4.1]).

Let `A = (A₁, …, A₄)` be a partition of `ℝ³` with `γ₃(Aᵢ) > 0` for all `i`, satisfying the critical
point condition (2.2) with `span(z₁, …, z₄)` of dimension `3`, the partitions classified by
Lemma 3.1. Then `∑_{i=1}^4 ‖zᵢ‖² < 9/(8π)`.

**Formalization Note.** The page says that Lemma 3.1 leaves only two partitions that could maximize
`F`, and that "they" satisfy the strict bound; "they" are the two critical partitions of Lemma 3.1,
so the bound is stated for every partition satisfying Lemma 3.1's hypotheses (`IsPartition`, (2.2)
as `A i =ᵐ closedCell z i`, span of dimension `3`, positive cells). -/
theorem case_k4_strict (A : Fin 4 → Set (Space 3)) (hA : IsPartition A)
    (hpos : ∀ i, 0 < gaussian 3 (A i))
    (hcrit : ∀ i, A i =ᵐ[gaussian 3] closedCell (fun j => centroid (A j)) i)
    (hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range fun j => centroid (A j))) = 3) :
    value A < 9 / (8 * Real.pi) := by sorry

end HeilmanPropeller
