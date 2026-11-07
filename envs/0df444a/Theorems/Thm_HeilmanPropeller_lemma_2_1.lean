-- Prove2me | Theorems.Thm_HeilmanPropeller_lemma_2_1
-- name    : HeilmanPropeller.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:06.148974+00:00
-- url     : https://prove2.me/theorems/a5f80f72-3e96-4732-898a-a014ca6929d6
-- title:
--   Lemma 2.1: first variation of an optimal Gaussian partition
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Fix $n\ge1$ and $N\ge2$.
--
--   1. There is a measurable partition of $\mathbb R^n$ into $k\le N$ sets maximizing $F$ among partitions of $\mathbb R^n$ into $N$ sets.
--   2. Let $k\le N$ and let $\mathcal A=(A_1,\dots,A_k)$ be any such maximizing partition with $\gamma_n(A_i)>0$ for all $i$. Then
--
--   $$\sum_{i=1}^k z_i=0,\qquad \langle z_i,z_j\rangle<0\quad(i\ne j);$$
--
--   the span of $z_1,\dots,z_k$ has dimension $k-1$; up to null sets
--
--   $$A_i=\{x\in\mathbb R^n:\ \langle z_i,x\rangle=\max_{j}\langle z_j,x\rangle\};$$
--
--   $k\ge2$; and $\max_{\mathcal A\subseteq\mathbb R^n,|\mathcal A|\le N}F=\max_{\mathcal A\subseteq\mathbb R^{k-1},|\mathcal A|=k}F$: there is a partition $\mathcal B$ of $\mathbb R^{k-1}$ into $k$ sets of positive measure with $F(\mathcal B)=F(\mathcal A)$ that maximizes $F$ among partitions of $\mathbb R^{k-1}$ into $k$ sets.
--
--   The lemma is the first-variation analysis of an optimal partition without the minimality assumption of Khot–Naor: optimal cells are Voronoi cones of their moments, and the problem reduces to $\mathbb R^{k-1}$.
--
--   **Formalization Note** $\{\langle z_i,x\rangle=\max_j\langle z_j,x\rangle\}$ is the reused `closedCell z i`; "up to sets of measure zero" is almost-everywhere equality of sets.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: "There exists a measurable partition … maximizing F(A) among partitions of ℝⁿ into N sets" → ∃ k A, MaximizesAmong N A, with A and its competitors IsPartitions (a.e.-partitions); reason: reassigning a null set turns an a.e.-partition into an exact one without changing any moment, so the maximum over a.e.-partitions equals the paper's maximum and an a.e. maximizer gives an exact one
--   - encoding: ⟨zᵢ, zⱼ⟩ < 0 for 1 ≤ i < j ≤ k → for all i ≠ j; reason: the inner product is symmetric
--   - encoding: (2.2) up to sets of measure zero → A i =ᵐ[gaussian n] closedCell z i; reason: a.e. equality of sets is "up to measure zero"
--   - reading: "After applying a rotation to ℝⁿ and projecting onto the span of z₁, …, z_k, we may assume that n = k − 1 … That is, max_{|A|≤N} F = max_{A ⊆ ℝ^{k−1}, |A| = k} F" → there is B : Fin k → Set (Space (k − 1)) with MaximizesAmong k B, all cells of positive measure, and value B = value A; reason: the equality of maxima, attained by the projected partition, which keeps its k positive cells
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 2.1, p.4

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_HeilmanPropeller_MaximizesAmong

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller
open OAI.GaussianPropeller.Reduction (closedCell)
open scoped RealInnerProductSpace

/-- **Lemma 2.1 (first variation).** Heilman, *On the Propeller Conjecture*, arXiv:2610.32158
(held version, sha256 13f5ddf8…), Lemma 2.1, p.4.

Fix `n ≥ 1`, `N ≥ 2`.
1. There is a partition of `ℝⁿ` into `k ≤ N` sets maximizing `F` among partitions of `ℝⁿ` into `N`
   sets.
2. Let `A = (A₁, …, A_k)`, `k ≤ N`, be any such maximizing partition with `γₙ(Aᵢ) > 0` for all `i`,
   and `zᵢ = ∫_{Aᵢ} x dγₙ(x)`. Then `∑ zᵢ = 0` and `⟨zᵢ, zⱼ⟩ < 0` for `i ≠ j` (2.1); the span of the
   `zᵢ` has dimension `k − 1`; up to null sets `Aᵢ = {x : ⟨zᵢ, x⟩ = maxⱼ ⟨zⱼ, x⟩}` (2.2); `k ≥ 2`;
   and `max_{A ⊆ ℝⁿ, |A| ≤ N} F(A) = max_{A ⊆ ℝ^{k−1}, |A| = k} F(A)`.

**Formalization Note.**
* `MaximizesAmong N A`: `A` is an `IsPartition` (a.e.-partition) into `k ≤ N` cells whose value is
  at least that of every `N`-cell partition of `ℝⁿ`.
* `closedCell z i = {x | ∀ j, ⟪z j, x⟫ ≤ ⟪z i, x⟫}` (reused) is the set in (2.2).
* `⟨zᵢ, zⱼ⟩ < 0` is stated for all `i ≠ j`, the same as `i < j` by symmetry.
* The last clause "after a rotation and projection we may assume `n = k − 1`", i.e. the equality of
  maxima, is: there is a partition `B` of `ℝ^{k−1}` into `k` cells, all of positive measure, with
  `F(B) = F(A)` that maximizes `F` among `k`-cell partitions of `ℝ^{k−1}`. -/
theorem lemma_2_1 (n N : ℕ) (hn : 1 ≤ n) (hN : 2 ≤ N) :
    (∃ (k : ℕ) (A : Fin k → Set (Space n)), MaximizesAmong N A) ∧
    ∀ (k : ℕ) (A : Fin k → Set (Space n)), MaximizesAmong N A →
      (∀ i, 0 < gaussian n (A i)) →
      let z : Fin k → Space n := fun i => centroid (A i)
      ∑ i, z i = 0 ∧ (∀ i j, i ≠ j → ⟪z i, z j⟫ < 0) ∧
      Module.finrank ℝ (Submodule.span ℝ (Set.range z)) = k - 1 ∧
      (∀ i, A i =ᵐ[gaussian n] closedCell z i) ∧ 2 ≤ k ∧
      ∃ B : Fin k → Set (Space (k - 1)), MaximizesAmong k B ∧
        (∀ i, 0 < gaussian (k - 1) (B i)) ∧ value B = value A := by sorry

end HeilmanPropeller
