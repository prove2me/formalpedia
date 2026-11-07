-- Prove2me | Theorems.Thm_GaussPart_lemma_3_11
-- name    : GaussPart.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:27.262141+00:00
-- url     : https://prove2.me/theorems/f2d18edf-bf3b-491c-bc68-f32d8ec9b7c0
-- title:
--   Lemma 3.11 — conditional smoothness on most cells
-- statement:
--   Let $P,Q$ be probability distributions on $\mathbb R^d$, $q\ge1$, $\sigma,\eta\in(0,1)$, and let $Q$ be $(q,\sigma)$-smooth with respect to $P$. For every finite measurable partition $\mathcal P$ of $\mathbb R^d$ there is a collection $\mathcal G\subseteq\mathcal P$ of cells of positive $Q$-mass with
--   $$\sum_{R\in\mathcal G}Q(R)\ge1-\eta,$$
--   such that for every $R\in\mathcal G$ the conditional distribution $Q\mid R$ is $(2q,\sigma\eta/(2q))$-smooth with respect to $P\mid R$.
--
--   Smoothness is not inherited by conditional distributions in general; the lemma shows it survives, with worse parameters, on all but $\eta$ of the mass, which is what allows Algorithm 1 to discard rejected cells.
--
--   **Formalization Note** The partition is a family of measurable, pairwise disjoint sets indexed by a finite type and covering $\mathbb R^d$; $\mathcal G$ is a set of indices. Conditional laws are `ProbabilityTheory.cond`.
--
--   Differences from the source:
--   - encoding: a finite measurable partition 𝒫 and G ⊆ 𝒫 → a finite indexed family of measurable, pairwise disjoint sets covering ℝ^d, and a finite set of indices; reason: repeated cells can only be empty, of Q-mass 0, so never in G
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.11, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_Cell

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.11** (Conditional smoothness on most cells).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.11, p.25 (PDF p.27).

"Let P, Q be probability distributions on ℝ^d, let q ≥ 1 and σ, η ∈ (0, 1), and suppose that Q is
(q, σ)-smooth with respect to P. For every finite measurable partition 𝒫 of ℝ^d, there is a
collection G ⊆ 𝒫 of cells of positive Q-mass such that ∑_{R∈G} Q(R) ≥ 1 − η, and, for every R ∈ G,
the conditional distribution Q | R is (2q, ση/(2q))-smooth with respect to P | R."

**Formalization Note.** The finite measurable partition is a family `cells : ι → Set (ℝ^d)` over a
finite index type, of measurable, pairwise disjoint sets covering `ℝ^d`; `G` is a set of indices.
`P` is any probability measure, not only the Gaussian. Conditional laws are
`ProbabilityTheory.cond`. -/
theorem lemma_3_11 {d : ℕ} (P Q : Measure (Vec d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (q σ η : ℝ) (hq : 1 ≤ q) (hσ : 0 < σ) (hσ1 : σ < 1) (hη : 0 < η)
    (hη1 : η < 1) (hs : IsSmooth P Q q σ) {ι : Type*} [Fintype ι] (cells : ι → Set (Vec d))
    (hmeas : ∀ i, MeasurableSet (cells i)) (hdisj : Pairwise (Function.onFun Disjoint cells))
    (hcover : ⋃ i, cells i = Set.univ) :
    ∃ G : Finset ι, (∀ i ∈ G, 0 < Q (cells i)) ∧
      1 - η ≤ ∑ i ∈ G, (Q (cells i)).toReal ∧
      ∀ i ∈ G, IsSmooth (ProbabilityTheory.cond P (cells i)) (ProbabilityTheory.cond Q (cells i))
        (2 * q) (σ * η / (2 * q)) := by sorry

end GaussPart
