-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_corollary_2_3
-- name    : KallMayerSLP.RecourseBounds.corollary_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:20.945206+00:00
-- url     : https://prove2.me/theorems/a7b08f2e-491b-4ac2-b55b-b08f9af1b641
-- title:
--   Corollary 2.3 — refining the partition improves both bounds
-- statement:
--   Under the assumptions of Lemma 2.8, let $\mathcal Y$ be a partition of $\Xi$ that refines the partition $\mathcal X$ (each cell of $\mathcal X$ is a union of cells of $\mathcal Y$). With $\mathbb P_{\eta_{\mathcal X}}$ the Jensen distribution and $\mathbb Q_{\eta_{\mathcal X}}=\sum_k\pi_k\mathbb Q_k$ the E–M distribution of a partition,
--   $$
--   \int_\Xi\varphi(\eta)\,\mathbb P_{\eta_{\mathcal X}}(d\eta)\le\int_\Xi\varphi(\eta)\,\mathbb P_{\eta_{\mathcal Y}}(d\eta)\le\mathbb E_\xi[\varphi(\xi)]
--   $$
--   and
--   $$
--   \mathbb E_\xi[\varphi(\xi)]\le\int_\Xi\varphi(\eta)\,\mathbb Q_{\eta_{\mathcal Y}}(d\eta)\le\int_\Xi\varphi(\eta)\,\mathbb Q_{\eta_{\mathcal X}}(d\eta).
--   $$
--
--   So along successive refinements the Jensen bound increases and the E–M bound decreases.
--
--   **Formalization Note** The two integrals are `jensenPartitionBound` and `emPartitionBound`.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: φ : Ξ → ℝ convex → φ : (Fin r → ℝ) → ℝ with ConvexOn ℝ (Set.Icc α β) φ; reason: values outside Ξ never enter the statement
--   - reading: cells Ξₖ ≠ ∅ are half-open or closed intervals → each cell is a product of one-dimensional intervals [lo, hi], [lo, hi) or (lo, hi], the kind chosen per coordinate; reason: the strongest reading: it contains every narrower reading of 'half-open or closed intervals' of ℝ^r
--   - generalization: Q_k, the E–M distribution on the cell Ξₖ ((2.30) on the cell), divides by the cell's side lengths → a closed cell with a degenerate side lo = hi is allowed, with the point-mass convention of vertexProb; reason: for nondegenerate cells the Lean weights are the book's (2.30), so the statement specializes to the book's
--   - encoding: πₖ φ(IE[ξ | ξ ∈ Ξₖ]), πₖ IE[φ(ξ) | ξ ∈ Ξₖ], πₖ ∫ φ dQ_k → P.real (cell k) * φ(⨍ x in cell k, x ∂P), ∫ x in cell k, φ x ∂P, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ; reason: equal for πₖ > 0; a cell with πₖ = 0 has undefined conditional quantities and contributes 0 (paper.md reading 5)
--   - encoding: Y a refinement of X: each cell of X is the union of one or several cells of Y → IsRefinement cellX cellY: each cellX k is ⋃_{l ∈ s} cellY l for a finite s; reason: the book's definition; 'one or several' holds automatically for nonempty cells
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Corollary 2.3, p.223 (PDF 232)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_IsBoxPartition
import Definitions.Def_KallMayerSLP_RecourseBounds_IsRefinement
import Definitions.Def_KallMayerSLP_RecourseBounds_jensenPartitionBound
import Definitions.Def_KallMayerSLP_RecourseBounds_emPartitionBound

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Corollary 2.3 — refining the partition improves both bounds.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Corollary 2.3, printed p.223
(PDF 232): "Under the above assumptions, the partition `Y` of `Ξ` being a refinement of the partition
`X` implies
`∫_Ξ φ(η) IP_{η_X}(dη) ≤ ∫_Ξ φ(η) IP_{η_Y}(dη) ≤ IE_ξ[φ(ξ)]` and
`IE_ξ[φ(ξ)] ≤ ∫_Ξ φ(η) Q_{η_Y}(dη) ≤ ∫_Ξ φ(η) Q_{η_X}(dη)`
and hence an increasing lower and a decreasing upper bound."
"The above assumptions" (pp.221–223): `supp IP_ξ ⊂ Ξ = ×ᵢ [αᵢ, βᵢ]`, `φ : Ξ → ℝ` convex, `X`, `Y`
partitions of `Ξ` into nonempty half-open or closed interval cells.

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`.
`∫ φ dIP_{η_X}` is `jensenPartitionBound P cellX φ` (`Σₖ πₖ φ(IE[ξ | Ξₖ])`) and `∫ φ dQ_{η_X}` is
`emPartitionBound P loX hiX cellX φ` (`Σₖ πₖ ∫ φ dQ_k`). `Y` refines `X`: every cell of `X` is a union
of cells of `Y`. -/
theorem corollary_2_3 {r K L : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (loX hiX : Fin K → Fin r → ℝ) (cellX : Fin K → Set (Fin r → ℝ))
    (hX : IsBoxPartition α β loX hiX cellX)
    (loY hiY : Fin L → Fin r → ℝ) (cellY : Fin L → Set (Fin r → ℝ))
    (hY : IsBoxPartition α β loY hiY cellY)
    (hYX : IsRefinement cellX cellY)
    (φ : (Fin r → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.Icc α β) φ) :
    jensenPartitionBound P cellX φ ≤ jensenPartitionBound P cellY φ ∧
    jensenPartitionBound P cellY φ ≤ ∫ x, φ x ∂P ∧
    ∫ x, φ x ∂P ≤ emPartitionBound P loY hiY cellY φ ∧
    emPartitionBound P loY hiY cellY φ ≤ emPartitionBound P loX hiX cellX φ := by sorry

end KallMayerSLP.RecourseBounds
