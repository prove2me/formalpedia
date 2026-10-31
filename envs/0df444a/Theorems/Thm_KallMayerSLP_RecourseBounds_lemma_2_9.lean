-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_lemma_2_9
-- name    : KallMayerSLP.RecourseBounds.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:33.400888+00:00
-- url     : https://prove2.me/theorems/1f15d80f-06cf-46d5-9a37-039dcebede6d
-- title:
--   Lemma 2.9 — the Jensen and E–M bounds converge as the grid width tends to zero
-- statement:
--   Let $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$ and let $\varphi:\Xi\to\mathbb R$ be **continuous** (not necessarily convex). Let $\{\mathcal X^\nu\}$ be a sequence of successively refined partitions of $\Xi$ into interval cells with $\lim_{\nu\to\infty}\operatorname{grid}\mathcal X^\nu=0$. Then the corresponding Jensen and E–M approximations converge:
--   $$
--   \lim_{\nu\to\infty}\int_\Xi\varphi(\xi)\,\mathbb P_{\eta_{\mathcal X^\nu}}(d\xi)=\lim_{\nu\to\infty}\int_\Xi\varphi(\xi)\,\mathbb Q_{\eta_{\mathcal X^\nu}}(d\xi)=\int_\Xi\varphi(\xi)\,\mathbb P_\xi(d\xi).
--   $$
--
--   Together with Corollary 2.3 this makes the partitioned bounds a convergent bracketing scheme for $\mathbb E_\xi[\varphi(\xi)]$.
--
--   **Formalization Note** "Successively refined" is: $\mathcal X^{\nu+1}$ refines $\mathcal X^\nu$ for every $\nu$. The grid width uses sup-norm diameters.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: φ : Ξ → ℝ continuous → ContinuousOn φ (Set.Icc α β); reason: values outside Ξ never enter
--   - reading: cells Ξₖ ≠ ∅ are half-open or closed intervals → each cell is a product of one-dimensional intervals [lo, hi], [lo, hi) or (lo, hi], the kind chosen per coordinate; reason: the strongest reading: it contains every narrower reading of 'half-open or closed intervals' of ℝ^r
--   - generalization: Q_k, the E–M distribution on the cell Ξₖ ((2.30) on the cell), divides by the cell's side lengths → a closed cell with a degenerate side lo = hi is allowed, with the point-mass convention of vertexProb; reason: for nondegenerate cells the Lean weights are the book's (2.30), so the statement specializes to the book's
--   - encoding: πₖ φ(IE[ξ | ξ ∈ Ξₖ]), πₖ IE[φ(ξ) | ξ ∈ Ξₖ], πₖ ∫ φ dQ_k → P.real (cell k) * φ(⨍ x in cell k, x ∂P), ∫ x in cell k, φ x ∂P, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ; reason: equal for πₖ > 0; a cell with πₖ = 0 has undefined conditional quantities and contributes 0 (paper.md reading 5)
--   - encoding: diam Ξₖ = sup{‖ξ − η‖} (norm unnamed) → Metric.diam for the sup norm of Fin r → ℝ; reason: all norms on ℝ^r are equivalent, so grid X^ν → 0 does not depend on the norm
--   - encoding: a sequence {X^ν} of successively refined partitions → IsBoxPartition α β (lo ν) (hi ν) (cell ν) and IsRefinement (cell ν) (cell (ν+1)) for every ν; reason: each partition refines its predecessor, the book's 'successively refined'
--   - encoding: lim ∫φ dIP_{η_{X^ν}} = lim ∫φ dQ_{η_{X^ν}} = ∫φ dIP_ξ → both sequences tend to ∫ φ dP; reason: the book's chain of equal limits
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Lemma 2.9, p.224 (PDF 233)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_IsBoxPartition
import Definitions.Def_KallMayerSLP_RecourseBounds_IsRefinement
import Definitions.Def_KallMayerSLP_RecourseBounds_jensenPartitionBound
import Definitions.Def_KallMayerSLP_RecourseBounds_emPartitionBound
import Definitions.Def_KallMayerSLP_RecourseBounds_gridWidth

open MeasureTheory Filter Topology

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Lemma 2.9 — both bounds converge as the grid width tends to zero.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.9, printed p.224 (PDF 233):
"Let `supp IP_ξ ⊆ Ξ = ×_{i=1}^r [αᵢ, βᵢ]` and `φ : Ξ → ℝ` be continuous. Assume a sequence `{X^ν}`
of successively refined partitions of `Ξ` to be given such that `lim_{ν→∞} grid X^ν = 0`. Then, for
`{IP_{η_{X^ν}}}` and `{Q_{η_{X^ν}}}` the corresponding sequences of Jensen distributions and E–M
distributions, respectively, follows
`lim_{ν→∞} ∫_Ξ φ(ξ) IP_{η_{X^ν}}(dξ) = lim_{ν→∞} ∫_Ξ φ(ξ) Q_{η_{X^ν}}(dξ) = ∫_Ξ φ(ξ) IP_ξ(dξ)`."

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`.
`φ` is only continuous on `Ξ` (not convex). Partition `ν` has `K ν` cells `cell ν k` with closures
`[lo ν k, hi ν k]` (`IsBoxPartition`); "successively refined" is `IsRefinement (cell ν) (cell (ν+1))`
for every `ν`; `grid X^ν` is `gridWidth (cell ν)` (sup-norm diameters; the limit `0` does not depend
on the norm). The Jensen and E–M values are `jensenPartitionBound` and `emPartitionBound`; the
statement asserts that both sequences converge to `∫ φ dP`. -/
theorem lemma_2_9 {r : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (φ : (Fin r → ℝ) → ℝ) (hφ : ContinuousOn φ (Set.Icc α β))
    (K : ℕ → ℕ) (lo hi : (ν : ℕ) → Fin (K ν) → Fin r → ℝ)
    (cell : (ν : ℕ) → Fin (K ν) → Set (Fin r → ℝ))
    (hX : ∀ ν, IsBoxPartition α β (lo ν) (hi ν) (cell ν))
    (hrefine : ∀ ν, IsRefinement (cell ν) (cell (ν + 1)))
    (hgrid : Tendsto (fun ν => gridWidth (cell ν)) atTop (𝓝 0)) :
    Tendsto (fun ν => jensenPartitionBound P (cell ν) φ) atTop (𝓝 (∫ x, φ x ∂P)) ∧
    Tendsto (fun ν => emPartitionBound P (lo ν) (hi ν) (cell ν) φ) atTop
      (𝓝 (∫ x, φ x ∂P)) := by sorry

end KallMayerSLP.RecourseBounds
