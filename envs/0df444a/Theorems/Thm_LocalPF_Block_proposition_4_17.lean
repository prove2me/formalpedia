-- Prove2me | Theorems.Thm_LocalPF_Block_proposition_4_17
-- name    : LocalPF.Block.proposition_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:09.42117+00:00
-- url     : https://prove2.me/theorems/cdb33a7b-cbff-4f0f-a2a9-3c9b4452ebaa
-- title:
--   Proposition 4.17, p. 55 — block filter stability from product initial laws, with integers α_K summing to at most Δ_𝒦^{n−s}
-- statement:
--   Consider the local model with $r\ge1$ and a partition $\mathcal K$ into nonempty blocks, with strictly positive, $\psi^v$-integrable observation densities and a fixed observation sequence. Suppose there is $\varepsilon>0$ with $\varepsilon\le p^v(x,z^v)\le\varepsilon^{-1}$ for all $v,x,z$, such that
--   $$\varepsilon>\varepsilon_0=\Big(1-\frac1{6\Delta^2}\Big)^{1/2\Delta},$$
--   and let $\beta=-\log 6\Delta^2(1-\varepsilon^{2\Delta})>0$. Then for any product probability measures $\mu=\bigotimes_{K\in\mathcal K}\mu^K$ and $\nu=\bigotimes_{K\in\mathcal K}\nu^K$,
--   $$\|\tilde{\mathsf F}_n\cdots\tilde{\mathsf F}_{s+1}\mu-\tilde{\mathsf F}_n\cdots\tilde{\mathsf F}_{s+1}\nu\|_J\le\frac4{\varepsilon^{2|\mathcal K|_\infty}}\operatorname{card}J\,e^{-\beta(n-s)}\sum_{K'\in\mathcal K}\alpha_{K'}\|\mu^{K'}-\nu^{K'}\|$$
--   for every $s<n$, $K\in\mathcal K$ and $J\subseteq K$, where $(\alpha_{K'})_{K'\in\mathcal K}$ are nonnegative integers depending on $J$ and $n-s$ only, with $\sum_{K'}\alpha_{K'}\le\Delta_{\mathcal K}^{n-s}$.
--
--   This stability estimate for the block filter is the ingredient through which the one-step sampling errors are propagated in time without accumulation.
--
--   **Formalization Note** The quantifier order encodes "depending on $J$ and $n-s$ only": the integers $\alpha$ are chosen after the graph, $r$, the partition, $K$, $J$ and $m=n-s\ge1$, and before the state spaces, the reference measures, the densities, $\varepsilon$, the observations, $s$, $\mu$ and $\nu$. The factor $e^{-\beta(n-s)}$ is written as $q^{n-s}$ with $q=6\Delta^2(1-\varepsilon^{2\Delta})$. As in Theorem 4.14, $g^v>0$ and $\psi^v$-integrability of $g^v(\cdot,y)$ are added so that the Bayes formula is well defined. The norms are in $[0,\infty]$.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 55, Proposition 4.17

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Proposition 4.17 (p. 55). Here `q = e^{-β}` with `β = -log 6Δ²(1 - ε^{2Δ})`, and
`m = n - s ≥ 1`; the integers `α_K` are chosen after the graph, the partition, `K`, `J` and `m`,
and before everything else. -/
theorem proposition_4_17 :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (r : ℕ), 1 ≤ r →
    ∀ {ι : Type} [Fintype ι] (blk : V → ι), Function.Surjective blk →
    ∀ (k : ι) (J : Finset V), J ⊆ block blk k → ∀ m : ℕ, 1 ≤ m →
    ∃ α : ι → ℕ, ∑ K, α K ≤ maxBlockNbhd G r blk ^ m ∧
    ∀ (Xs : V → Type) [∀ v, TopologicalSpace (Xs v)] [∀ v, PolishSpace (Xs v)]
      [∀ v, MeasurableSpace (Xs v)] [∀ v, BorelSpace (Xs v)]
      (Ys : V → Type) [∀ v, TopologicalSpace (Ys v)] [∀ v, PolishSpace (Ys v)]
      [∀ v, MeasurableSpace (Ys v)] [∀ v, BorelSpace (Ys v)]
      (ψ : ∀ v, Measure (Xs v)) [∀ v, SigmaFinite (ψ v)]
      (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ),
      IsLocalModel G r ψ p g →
      (∀ v ξ η, 0 < g v ξ η) → (∀ v η, Integrable (fun ξ => g v ξ η) (ψ v)) →
    ∀ ε : ℝ, 0 < ε → (∀ v x z, ε ≤ p v x z ∧ p v x z ≤ ε⁻¹) →
      (1 - 1 / (6 * (maxNbhd G r : ℝ) ^ 2)) ^ ((1 : ℝ) / (2 * (maxNbhd G r : ℝ))) < ε →
    ∀ (y : ℕ → ∀ v, Ys v) (s : ℕ) (μK νK : ∀ k, Measure (∀ v : {v // blk v = k}, Xs v.1)),
      (∀ k, IsProbabilityMeasure (μK k)) → (∀ k, IsProbabilityMeasure (νK k)) →
      let q : ℝ := 6 * (maxNbhd G r : ℝ) ^ 2 * (1 - ε ^ (2 * maxNbhd G r))
      locTV (J : Set V) (blockFiltFrom ψ p g blk y s (blockProd blk μK) m)
          (blockFiltFrom ψ p g blk y s (blockProd blk νK) m) ≤
        ENNReal.ofReal (4 / ε ^ (2 * maxBlock blk) * J.card * q ^ m) *
          ∑ K, (α K : ℝ≥0∞) * tv (μK K) (νK K) := by sorry

end LocalPF.Block
