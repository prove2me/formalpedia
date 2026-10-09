-- Prove2me | Theorems.Thm_LocalPF_Block_lemma_4_19
-- name    : LocalPF.Block.lemma_4_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:39.13798+00:00
-- url     : https://prove2.me/theorems/6b277d16-62db-4548-ba63-3415e14fe2ab
-- title:
--   Lemma 4.19, p. 57 — one-step sampling error at s = n: |||F̃_n ρ − F̂_n ρ|||_K ≤ 2κ^{−2|𝒦|∞}/√N
-- statement:
--   Consider the local model with a partition $\mathcal K$ into nonempty blocks, and suppose there is $\kappa>0$ with
--   $$\kappa\le g^v(x^v,y^v)\le\kappa^{-1}\qquad\text{for all }v\in V,\ x\in\mathbb X,\ y\in\mathbb Y.$$
--   Let $N\ge1$, let $Y_n$ be any observation and $\rho$ any probability measure on $\mathbb X$. Compare $\tilde{\mathsf F}_n\rho=\mathsf C_n\mathsf B\mathsf P\rho$ with the random measure $\hat{\mathsf F}_n\rho=\mathsf C_n\mathsf B\mathsf S^N\mathsf P\rho$, where $\mathsf S^N\mathsf P\rho=\frac1N\sum_{i=1}^N\delta_{x(i)}$ for i.i.d. samples $x(1),\dots,x(N)\sim\mathsf P\rho$. Then for every block $K\in\mathcal K$ and every measurable $f\in\mathbb X^K$ with $|f|\le1$,
--   $$\mathbf E\big[|\tilde{\mathsf F}_n\rho(f)-\hat{\mathsf F}_n\rho(f)|^2\big]^{1/2}\le\frac{2\kappa^{-2|\mathcal K|_\infty}}{\sqrt N},$$
--   that is, $\max_{K\in\mathcal K}|||\tilde{\mathsf F}_n\rho-\hat{\mathsf F}_n\rho|||_K\le 2\kappa^{-2|\mathcal K|_\infty}/\sqrt N$.
--
--   This bounds the sampling error of the last step of the block particle filter, locally on a block, independently of the dimension.
--
--   **Formalization Note** The paper states the bound with $\rho=\hat\pi^\mu_{n-1}$, the (random) previous output of the algorithm; the statement here holds for every deterministic probability measure $\rho$, which gives the paper's by conditioning on $\hat\pi^\mu_{n-1}$ (a disclosed strengthening). $|||\cdot|||_K$ is written in the "for every test function" form with the square cleared; the expectation is a lower Lebesgue integral of a nonnegative quantity, over the $N$ i.i.d. samples. The standing model assumptions of the Setting file (densities, locality) are included.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 57, Lemma 4.19

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Lemma 4.19 (Sampling error, s = n), p. 57, for an arbitrary probability measure `ρ` in
place of `π̂^µ_{n-1}`: `𝖥̃_n ρ = 𝖢_n 𝖡 𝖯 ρ` against `𝖥̂_n ρ = 𝖢_n 𝖡 𝖲^N 𝖯 ρ`, the expectation
being over the `N` i.i.d. samples from `𝖯 ρ`; `Y_n` is the observation `yn`. -/
theorem lemma_4_19 {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r)
    {Xs : V → Type*} [∀ v, TopologicalSpace (Xs v)] [∀ v, PolishSpace (Xs v)]
    [∀ v, MeasurableSpace (Xs v)] [∀ v, BorelSpace (Xs v)]
    {Ys : V → Type*} [∀ v, TopologicalSpace (Ys v)] [∀ v, PolishSpace (Ys v)]
    [∀ v, MeasurableSpace (Ys v)] [∀ v, BorelSpace (Ys v)]
    (ψ : ∀ v, Measure (Xs v)) [∀ v, SigmaFinite (ψ v)]
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ)
    (hM : IsLocalModel G r ψ p g)
    {ι : Type*} [Fintype ι] (blk : V → ι) (hblk : Function.Surjective blk)
    (κ : ℝ) (hκ : 0 < κ) (hg : ∀ v ξ η, κ ≤ g v ξ η ∧ g v ξ η ≤ κ⁻¹)
    (N : ℕ) (hN : 1 ≤ N) (yn : ∀ v, Ys v) (ρ : Measure (∀ v, Xs v)) [IsProbabilityMeasure ρ]
    (k : ι) (f : (∀ v, Xs v) → ℝ) (hf : IsTest (block blk k : Set V) f) :
    ∫⁻ a, ENNReal.ofReal ((∫ z, f z ∂(correct g yn (blocking blk (predict ψ p ρ))) -
        ∫ z, f z ∂(correct g yn (blocking blk (empirical a)))) ^ 2)
      ∂(Measure.pi fun _ : Fin N => predict ψ p ρ) ≤
      ENNReal.ofReal ((2 * (κ ^ (2 * maxBlock blk))⁻¹ / Real.sqrt N) ^ 2) := by sorry

end LocalPF.Block
