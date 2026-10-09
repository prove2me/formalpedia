-- Prove2me | Theorems.Thm_LocalPF_Block_theorem_4_23
-- name    : LocalPF.Block.theorem_4_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:45.125246+00:00
-- url     : https://prove2.me/theorems/2770ef60-5df9-4726-bd1b-3a997ffe6105
-- title:
--   Theorem 4.23, p. 61 — variance term: |||π̃^x_n − π̂^x_n|||_J ≤ card J · 64Δ_𝒦e^β(1−e^{−β})⁻¹ ε^{−4|𝒦|∞}κ^{−4|𝒦|∞Δ_𝒦}/√N
-- statement:
--   Consider the local model with $r\ge1$ and a partition $\mathcal K$ into nonempty blocks, $N\ge1$ particles, and a fixed observation sequence. Suppose there are $\varepsilon,\kappa>0$ with
--   $$\varepsilon\le p^v(x,z^v)\le\varepsilon^{-1},\qquad\kappa\le g^v(x^v,y^v)\le\kappa^{-1}\qquad\forall v\in V,\ x,z\in\mathbb X,\ y\in\mathbb Y,$$
--   such that
--   $$\varepsilon>\varepsilon_0=\Big(1-\frac1{6\Delta_{\mathcal K}\Delta^2}\Big)^{1/2\Delta}.$$
--   Let $\beta=-\log 6\Delta_{\mathcal K}\Delta^2(1-\varepsilon^{2\Delta})>0$. Then
--   $$|||\tilde\pi^x_n-\hat\pi^x_n|||_J\le\operatorname{card}J\,\frac{64\Delta_{\mathcal K}e^{\beta}}{1-e^{-\beta}}\,\frac{\varepsilon^{-4|\mathcal K|_\infty}\kappa^{-4|\mathcal K|_\infty\Delta_{\mathcal K}}}{\sqrt N}$$
--   for every $n\ge0$, $x\in\mathbb X$, $K\in\mathcal K$ and $J\subseteq K$. Here $\tilde\pi^x_n$ is the block filter, $\hat\pi^x_n$ the block particle filter, both started at $\delta_x$, and $|||\rho-\rho'|||_J=\sup_{f\in\mathbb X^J,|f|\le1}\mathbf E[|\rho(f)-\rho'(f)|^2]^{1/2}$ with the expectation over the random sampling of the algorithm. Moreover the law of the particle arrays is a probability measure.
--
--   This is the variance half of the main theorem: the Monte Carlo error of the block particle filter is controlled locally, uniformly in time, with a constant exponential in the block size but not in the dimension.
--
--   **Formalization Note** The bound is stated for every test function $f\in\mathbb X^J$ with $|f|\le1$, with the square cleared, and the expectation is a lower Lebesgue integral against the law of the step-$n$ particle array of the algorithm; the bound holds for every observation sequence (Remark 2.4). The conjunct that this law is a probability measure rules out a degenerate zero law. The hypothesis $\varepsilon<1$ is added: at $\varepsilon=1$ the paper's $\beta$ is $+\infty$ and its bound is $+\infty$ (no content), while $-\log 0$ is not representable in $\mathbb R$.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 61, Theorem 4.23

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Theorem 4.23 (Variance term), p. 61, in the `∀ f` form of `|||·|||_J` with the square
cleared, the expectation being over the particle arrays of the block particle filter. -/
theorem theorem_4_23 {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r)
    {Xs : V → Type*} [∀ v, TopologicalSpace (Xs v)] [∀ v, PolishSpace (Xs v)]
    [∀ v, MeasurableSpace (Xs v)] [∀ v, BorelSpace (Xs v)]
    {Ys : V → Type*} [∀ v, TopologicalSpace (Ys v)] [∀ v, PolishSpace (Ys v)]
    [∀ v, MeasurableSpace (Ys v)] [∀ v, BorelSpace (Ys v)]
    (ψ : ∀ v, Measure (Xs v)) [∀ v, SigmaFinite (ψ v)]
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ)
    (hM : IsLocalModel G r ψ p g)
    {ι : Type*} [Fintype ι] (blk : V → ι) (hblk : Function.Surjective blk)
    (ε κ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hκ : 0 < κ)
    (hp : ∀ v x z, ε ≤ p v x z ∧ p v x z ≤ ε⁻¹) (hg : ∀ v ξ η, κ ≤ g v ξ η ∧ g v ξ η ≤ κ⁻¹)
    (hε₀ : (1 - 1 / (6 * (maxBlockNbhd G r blk : ℝ) * (maxNbhd G r : ℝ) ^ 2)) ^
      ((1 : ℝ) / (2 * (maxNbhd G r : ℝ))) < ε)
    (N : ℕ) (hN : 1 ≤ N) (y : ℕ → ∀ v, Ys v) (x : ∀ v, Xs v) (n : ℕ) (k : ι) (J : Finset V)
    (hJ : J ⊆ block blk k) :
    let Δ := maxNbhd G r
    let ΔK := maxBlockNbhd G r blk
    let β : ℝ := -Real.log (6 * (ΔK : ℝ) * (Δ : ℝ) ^ 2 * (1 - ε ^ (2 * Δ)))
    IsProbabilityMeasure (bpfLaw ψ p g blk y x N n) ∧
    ∀ f : (∀ v, Xs v) → ℝ, IsTest (J : Set V) f →
      ∫⁻ a, ENNReal.ofReal ((∫ z, f z ∂(blockFilt ψ p g blk y x n) -
          ∫ z, f z ∂(bpf g blk y x N n a)) ^ 2) ∂(bpfLaw ψ p g blk y x N n) ≤
        ENNReal.ofReal ((J.card * (64 * ΔK * Real.exp β / (1 - Real.exp (-β))) *
          ((ε ^ (4 * maxBlock blk))⁻¹ * (κ ^ (4 * maxBlock blk * ΔK))⁻¹) / Real.sqrt N) ^ 2) := by sorry

end LocalPF.Block
