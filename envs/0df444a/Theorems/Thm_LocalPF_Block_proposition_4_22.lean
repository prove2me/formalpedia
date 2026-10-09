-- Prove2me | Theorems.Thm_LocalPF_Block_proposition_4_22
-- name    : LocalPF.Block.proposition_4_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:39.105612+00:00
-- url     : https://prove2.me/theorems/3d44c00a-2dc3-4f45-b285-ccc3df3448ae
-- title:
--   Proposition 4.22, p. 59 — one-step sampling error at s < n, in ‖·‖_K: 16Δ_𝒦 ε^{−2|𝒦|∞} κ^{−4|𝒦|∞Δ_𝒦}/√N
-- statement:
--   Consider the local model with $r\ge1$ and a partition $\mathcal K$ into nonempty blocks, and suppose there are $\varepsilon,\kappa>0$ with
--   $$\varepsilon\le p^v(x,z^v)\le\varepsilon^{-1},\qquad\kappa\le g^v(x^v,y^v)\le\kappa^{-1}\qquad\forall v\in V,\ x,z\in\mathbb X,\ y\in\mathbb Y.$$
--   Let $N\ge1$, fix an observation sequence and $s\ge1$, and let $\rho$ be any probability measure on $\mathbb X$. With $\hat{\mathsf F}_s\rho=\mathsf C_s\mathsf B\mathsf S^N\mathsf P\rho$ as in Lemma 4.19,
--   $$\max_{K\in\mathcal K}\mathbf E\big[\|\tilde{\mathsf F}_{s+1}\tilde{\mathsf F}_s\rho-\tilde{\mathsf F}_{s+1}\hat{\mathsf F}_s\rho\|_K^2\big]^{1/2}\le\frac{16\Delta_{\mathcal K}\,\varepsilon^{-2|\mathcal K|_\infty}\kappa^{-4|\mathcal K|_\infty\Delta_{\mathcal K}}}{\sqrt N},$$
--   the expectation being over the $N$ i.i.d. samples from $\mathsf P\rho$.
--
--   Keeping one step of block-filter dynamics after the sampling step lets the error be measured in the strong norm $\|\cdot\|_K$, as Proposition 4.17 requires.
--
--   **Formalization Note** The paper states the bound for $\rho=\hat\pi^\mu_{s-1}$ and $0<s<n$ ("applied conditionally given $\hat\pi^\mu_{s-1}$", p. 61); the statement here holds for every deterministic probability measure $\rho$ and every $s\ge1$ (the time $n$ plays no role beyond $s+1\le n$), a disclosed strengthening. The squared norm is in $[0,\infty]$ and the expectation is a lower Lebesgue integral; the bound is stated squared.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 59, Proposition 4.22

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Proposition 4.22 (Sampling error, s < n), p. 59, for an arbitrary probability measure `ρ` in
place of `π̂^µ_{s-1}`: `𝖥̃_{s+1} 𝖥̃_s ρ` against `𝖥̃_{s+1} 𝖥̂_s ρ`, the expectation being over the
`N` i.i.d. samples from `𝖯 ρ`. -/
theorem proposition_4_22 {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r)
    {Xs : V → Type*} [∀ v, TopologicalSpace (Xs v)] [∀ v, PolishSpace (Xs v)]
    [∀ v, MeasurableSpace (Xs v)] [∀ v, BorelSpace (Xs v)]
    {Ys : V → Type*} [∀ v, TopologicalSpace (Ys v)] [∀ v, PolishSpace (Ys v)]
    [∀ v, MeasurableSpace (Ys v)] [∀ v, BorelSpace (Ys v)]
    (ψ : ∀ v, Measure (Xs v)) [∀ v, SigmaFinite (ψ v)]
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ)
    (hM : IsLocalModel G r ψ p g)
    {ι : Type*} [Fintype ι] (blk : V → ι) (hblk : Function.Surjective blk)
    (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (hp : ∀ v x z, ε ≤ p v x z ∧ p v x z ≤ ε⁻¹) (hg : ∀ v ξ η, κ ≤ g v ξ η ∧ g v ξ η ≤ κ⁻¹)
    (N : ℕ) (hN : 1 ≤ N) (y : ℕ → ∀ v, Ys v) (s : ℕ) (hs : 1 ≤ s)
    (ρ : Measure (∀ v, Xs v)) [IsProbabilityMeasure ρ] (k : ι) :
    ∫⁻ a, locTV (block blk k : Set V)
        (correct g (y (s + 1)) (blocking blk (predict ψ p
          (correct g (y s) (blocking blk (predict ψ p ρ))))))
        (correct g (y (s + 1)) (blocking blk (predict ψ p
          (correct g (y s) (blocking blk (empirical a)))))) ^ 2
      ∂(Measure.pi fun _ : Fin N => predict ψ p ρ) ≤
      ENNReal.ofReal ((16 * maxBlockNbhd G r blk * (ε ^ (2 * maxBlock blk))⁻¹ *
        (κ ^ (4 * maxBlock blk * maxBlockNbhd G r blk))⁻¹ / Real.sqrt N) ^ 2) := by sorry

end LocalPF.Block
