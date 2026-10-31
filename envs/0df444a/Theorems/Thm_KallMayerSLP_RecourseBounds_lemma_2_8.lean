-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_lemma_2_8
-- name    : KallMayerSLP.RecourseBounds.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:52.838988+00:00
-- url     : https://prove2.me/theorems/33b6e555-9698-4b9a-a3dc-be4850c7bbf0
-- title:
--   Lemma 2.8 — Jensen and generalized E–M bounds on a partition of the support box
-- statement:
--   Let $\xi$ be a random vector with $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$ and mean $\bar\xi=\mathbb E_\xi[\xi]$, let $\varphi:\Xi\to\mathbb R$ be convex, and let $\mathcal X=\{\Xi_k;\ k=1,\dots,K\}$ be a partition of $\Xi$ into nonempty, pairwise disjoint, half-open or closed interval cells. Put $\pi_k=\mathbb P_\xi(\Xi_k)$. Let $\mathbb Q_k$ be the generalized E–M distribution of the conditional law of $\xi$ given $\xi\in\Xi_k$, on the vertices of the cell, and $\mathbb Q$ the generalized E–M distribution on $\Xi$ (Lemma 2.7). Then the lower bounds satisfy
--   $$
--   \varphi(\bar\xi)\le\sum_{k=1}^K\pi_k\,\varphi\big(\mathbb E_\xi[\xi\mid\xi\in\Xi_k]\big)\le\sum_{k=1}^K\pi_k\,\mathbb E_\xi[\varphi(\xi)\mid\xi\in\Xi_k]=\mathbb E_\xi[\varphi(\xi)] \tag{2.39}
--   $$
--   and the upper bounds satisfy
--   $$
--   \mathbb E_\xi[\varphi(\xi)]=\sum_{k=1}^K\pi_k\,\mathbb E_\xi[\varphi(\xi)\mid\xi\in\Xi_k]\le\sum_{k=1}^K\pi_k\int_{\Xi_k}\varphi(\eta)\,\mathbb Q_k(d\eta)\le\int_\Xi\varphi(\eta)\,\mathbb Q(d\eta). \tag{2.40}
--   $$
--
--   Partitioning the support thus tightens both the Jensen lower bound and the generalized Edmundson–Madansky upper bound, each of which needs only finitely many conditional moments; this is the basis of the discrete approximation methods for complete recourse problems.
--
--   **Formalization Note** The conditional quantities are multiplied out: $\pi_k\varphi(\mathbb E[\xi\mid\Xi_k])$ is $\pi_k\,\varphi(\bar\xi_k)$ with $\bar\xi_k$ the $\mathbb P_\xi$-average of $\xi$ over $\Xi_k$, $\pi_k\mathbb E[\varphi(\xi)\mid\Xi_k]$ is $\int_{\Xi_k}\varphi\,d\mathbb P$, and $\pi_k\int\varphi\,d\mathbb Q_k$ is the generalized E–M bound of $\mathbb P_\xi|_{\Xi_k}$ on the vertices of the closure $[\mathrm{lo}_k,\mathrm{hi}_k]$ of the cell. A cell with $\pi_k=0$ contributes $0$. The equality shared by (2.39) and (2.40) is stated once.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: φ : Ξ → ℝ convex → φ : (Fin r → ℝ) → ℝ with ConvexOn ℝ (Set.Icc α β) φ; reason: values outside Ξ never enter the statement
--   - reading: cells Ξₖ ≠ ∅ are half-open or closed intervals → each cell is a product of one-dimensional intervals [lo, hi], [lo, hi) or (lo, hi], the kind chosen per coordinate; reason: the strongest reading: it contains every narrower reading of 'half-open or closed intervals' of ℝ^r
--   - generalization: Q_k, the E–M distribution on the cell Ξₖ ((2.30) on the cell), divides by the cell's side lengths → a closed cell with a degenerate side lo = hi is allowed, with the point-mass convention of vertexProb; reason: for nondegenerate cells the Lean weights are the book's (2.30), so the statement specializes to the book's
--   - encoding: πₖ φ(IE[ξ | ξ ∈ Ξₖ]), πₖ IE[φ(ξ) | ξ ∈ Ξₖ], πₖ ∫ φ dQ_k → P.real (cell k) * φ(⨍ x in cell k, x ∂P), ∫ x in cell k, φ x ∂P, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ; reason: equal for πₖ > 0; a cell with πₖ = 0 has undefined conditional quantities and contributes 0 (paper.md reading 5)
--   - encoding: Q_k, the E–M distribution on Ξₖ → generalized E–M weights (2.30) of P.restrict (cell k) on the vertices of [lo k, hi k], the closure of the cell; reason: the closure of a nonempty interval cell is the closed box with the same endpoints
--   - encoding: the equality IE_ξ[φ(ξ)] = Σₖ πₖ IE_ξ[φ(ξ) | ξ ∈ Ξₖ] in both (2.39) and (2.40) → stated once; reason: the same equality
--   - generalization: Q, the E–M distribution (2.30) on Ξ, divides by βᵢ − αᵢ → a box Ξ with αᵢ = βᵢ is allowed, with the point-mass convention of vertexProb in genEMBound P α β; reason: for αᵢ < βᵢ the Lean weights are the book's (2.30), so the statement specializes to the book's
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Lemma 2.8, (2.39)–(2.40), p.222 (PDF 231); assumptions p.221 (PDF 230)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMBound
import Definitions.Def_KallMayerSLP_RecourseBounds_IsBoxPartition

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Lemma 2.8 — Jensen and generalized E–M bounds on a partition of the box.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.8, (2.39)–(2.40), printed
p.222 (PDF 231): "Under the above assumptions holds, with `πₖ = IP_ξ(Ξₖ)`, for the lower bounds of
`IE_ξ[φ(ξ)]`
`φ(ξ̄) ≤ Σ_{k=1}^K πₖ φ(IE_ξ[ξ | ξ ∈ Ξₖ]) ≤ Σ_{k=1}^K πₖ IE_ξ[φ(ξ) | ξ ∈ Ξₖ] = IE_ξ[φ(ξ)]` (2.39)
whereas for the upper bounds we get the inequalities
`IE_ξ[φ(ξ)] = Σ_{k=1}^K πₖ IE_ξ[φ(ξ) | ξ ∈ Ξₖ] ≤ Σ_{k=1}^K πₖ ∫_{Ξₖ} φ(η) Q_k(dη) ≤ ∫_Ξ φ(η) Q(dη)`,
(2.40) where `Q_k` is the E–M distribution on `Ξₖ` yielding `μ^k_Λ := IE_ξ[h_Λ(ξ) | ξ ∈ Ξₖ]` for all
`Λ ⊂ {1, ···, r}` and `k = 1, ···, K`, and `Q` is the E–M distribution on `Ξ` as described in
Lemma 2.7."
"The above assumptions" (p.221, PDF 230): `supp IP_ξ ⊂ Ξ = ×_{i=1}^r [αᵢ, βᵢ]`, `φ` convex,
`ξ̄ = IE_ξ[ξ]`, and a disjoint partition `X = {Ξₖ}` of `Ξ` into nonempty half-open or closed interval
cells.

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`; `φ`
is convex on `Ξ = Set.Icc α β` (values outside `Ξ` are irrelevant); cells are indexed by `Fin K`.
The conditional quantities are multiplied out: `πₖ φ(IE[ξ | Ξₖ])` is
`P.real (cell k) * φ (⨍ x in cell k, x ∂P)`, `πₖ IE[φ(ξ) | Ξₖ]` is `∫ x in cell k, φ x ∂P`, and
`πₖ ∫ φ dQ_k` is `genEMBound (P.restrict (cell k)) (lo k) (hi k) φ`, the generalized E–M bound
(2.30)–(2.31) of the cell's mass on the vertices of its closure `[lo k, hi k]`. A cell with
`πₖ = 0` contributes `0` to each sum (its conditional quantities are undefined in the book). `∫ φ dQ`
is `genEMBound P α β φ`. No integrability hypothesis: a function convex on a box is bounded and
Borel on it. -/
theorem lemma_2_8 {r K : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (lo hi : Fin K → Fin r → ℝ) (cell : Fin K → Set (Fin r → ℝ))
    (hX : IsBoxPartition α β lo hi cell)
    (φ : (Fin r → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.Icc α β) φ) :
    -- (2.39)
    φ (∫ x, x ∂P) ≤ ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) ∧
    ∑ k, P.real (cell k) * φ (⨍ x in cell k, x ∂P) ≤ ∑ k, ∫ x in cell k, φ x ∂P ∧
    ∑ k, ∫ x in cell k, φ x ∂P = ∫ x, φ x ∂P ∧
    -- (2.40)
    ∑ k, ∫ x in cell k, φ x ∂P ≤ ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ ∧
    ∑ k, genEMBound (P.restrict (cell k)) (lo k) (hi k) φ ≤ genEMBound P α β φ := by sorry

end KallMayerSLP.RecourseBounds
