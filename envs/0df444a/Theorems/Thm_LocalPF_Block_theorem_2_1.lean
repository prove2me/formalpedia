-- Prove2me | Theorems.Thm_LocalPF_Block_theorem_2_1
-- name    : LocalPF.Block.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:55.526959+00:00
-- url     : https://prove2.me/theorems/d86f7ed8-6118-4afd-9fb2-e81be2355c4f
-- title:
--   Theorem 2.1, pp. 16–17 — above a local mixing threshold, the block particle filter's local error is α card J [e^{−β₁d(J,∂K)} + e^{β₂|𝒦|∞}/√N], uniformly in time and dimension
-- statement:
--   This is the main result of Rebeschini and van Handel.
--
--   Let $G=(V,E)$ be a finite graph, $r\ge1$ a neighbourhood size, and consider the local hidden Markov model of the Setting file: Polish state and observation spaces $\mathbb X^v,\mathbb Y^v$, reference measures $\psi^v$, local transition densities $p^v(x,z^v)$ depending on $x$ only through $x^{N(v)}$, and observation densities $g^v(x^v,y^v)$. Let $\mathcal K$ be a partition of $V$ into nonempty blocks and $N\ge1$ the number of particles. Write $\Delta$, $\Delta_{\mathcal K}$, $|\mathcal K|_\infty$ for the local quantities and $\partial K$ for the $r$-inner boundary of a block.
--
--   **Theorem.** There exists a constant $0<\varepsilon_0<1$, depending only on $\Delta$ and $\Delta_{\mathcal K}$, such that the following holds. Suppose there exist $\varepsilon_0<\varepsilon<1$ and $0<\kappa<1$ such that
--   $$\varepsilon\le p^v(x,z^v)\le\varepsilon^{-1},\qquad\kappa\le g^v(x^v,y^v)\le\kappa^{-1}\qquad\forall v\in V,\ x,z\in\mathbb X,\ y\in\mathbb Y.$$
--   Then for every $n\ge0$, $x\in\mathbb X$, $K\in\mathcal K$ and $J\subseteq K$,
--   $$|||\pi^x_n-\hat\pi^x_n|||_J\le\alpha\operatorname{card}J\Big[e^{-\beta_1d(J,\partial K)}+\frac{e^{\beta_2|\mathcal K|_\infty}}{\sqrt N}\Big],$$
--   where the constants $0<\alpha,\beta_1,\beta_2<\infty$ depend only on $\varepsilon,\kappa,r,\Delta$ and $\Delta_{\mathcal K}$.
--
--   Here $\pi^x_n$ is the nonlinear filter and $\hat\pi^x_n$ the block particle filter (Algorithm 2), both started at $\delta_x$, and $|||\rho-\rho'|||_J=\sup_{f\in\mathbb X^J,|f|\le1}\mathbf E[|\rho(f)-\rho'(f)|^2]^{1/2}$.
--
--   The point of the theorem is that both the assumptions and the error bound involve only local quantities: neither depends on the time $n$ nor on the model dimension $\operatorname{card}V$. Choosing blocks of a suitable size balances the bias term (decaying in the distance to the block boundary) against the variance term (exponential in the block size), giving an error that is free of the curse of dimensionality.
--
--   **Formalization Note**
--   1. *Constants.* $\varepsilon_0$ is a function of $(\Delta,\Delta_{\mathcal K})$ and $\alpha,\beta_1,\beta_2$ are functions of $(\varepsilon,\kappa,r,\Delta,\Delta_{\mathcal K})$; all four are quantified before the graph, the state spaces, the model, the partition, $N$, the observations, $x$, $n$, $K$ and $J$, so they cannot depend on $\operatorname{card}V$ or on anything else.
--   2. *Observations.* Following Remark 2.4, the bound is stated for every fixed observation sequence, with the expectation over the random sampling of the algorithm only; $\pi^x_n$ is the filter recursion of p. 5 for that sequence. This is a strengthening of the averaged statement.
--   3. *Norm.* $|||\cdot|||_J\le B$ is stated as $\mathbf E[|\pi^x_n(f)-\hat\pi^x_n(f)|^2]\le B^2$ for every test function, the expectation being a lower Lebesgue integral against the law of the step-$n$ particle array; the statement also asserts that this law is a probability measure.
--   4. *Distance.* $e^{-\beta_1d(J,\partial K)}$ is $0$ when $d(J,\partial K)=+\infty$ (no path from $J$ to $\partial K$, or $\partial K=\varnothing$).
--   5. $r\ge1$ and $N\ge1$ are the paper's standing conventions; the reference measure of the observations and the normalisation of $g^v$ do not enter and are omitted.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), pp. 16–17, Theorem 2.1 (with Remark 2.4, p. 17)

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Theorem 2.1 (pp. 16–17), the main result. The constants are functions of the local
quantities only — `ε₀ = ε₀(Δ, Δ_𝒦)` and `α, β₁, β₂ = ·(ε, κ, r, Δ, Δ_𝒦)` — and are chosen before
the graph, the state spaces, the model, the partition, `N`, the observations, `x`, `n`, `K`, `J`.
`|||π^x_n − π̂^x_n|||_J ≤ B` is stated as `E[(π^x_n(f) − π̂^x_n(f))²] ≤ B²` for every test `f`. -/
theorem theorem_2_1 :
    ∃ ε₀ : ℕ → ℕ → ℝ, (∀ Δ ΔK, 0 < ε₀ Δ ΔK ∧ ε₀ Δ ΔK < 1) ∧
    ∃ α β₁ β₂ : ℝ → ℝ → ℕ → ℕ → ℕ → ℝ,
      (∀ ε κ r Δ ΔK, 0 < α ε κ r Δ ΔK ∧ 0 < β₁ ε κ r Δ ΔK ∧ 0 < β₂ ε κ r Δ ΔK) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (r : ℕ), 1 ≤ r →
    ∀ (Xs : V → Type) [∀ v, TopologicalSpace (Xs v)] [∀ v, PolishSpace (Xs v)]
      [∀ v, MeasurableSpace (Xs v)] [∀ v, BorelSpace (Xs v)]
      (Ys : V → Type) [∀ v, TopologicalSpace (Ys v)] [∀ v, PolishSpace (Ys v)]
      [∀ v, MeasurableSpace (Ys v)] [∀ v, BorelSpace (Ys v)]
      (ψ : ∀ v, Measure (Xs v)) [∀ v, SigmaFinite (ψ v)]
      (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ),
      IsLocalModel G r ψ p g →
    ∀ (ι : Type) [Fintype ι] (blk : V → ι), Function.Surjective blk →
    ∀ (N : ℕ), 1 ≤ N →
    ∀ ε κ : ℝ,
      ε₀ (maxNbhd G r) (maxBlockNbhd G r blk) < ε → ε < 1 → 0 < κ → κ < 1 →
      (∀ v x z, ε ≤ p v x z ∧ p v x z ≤ ε⁻¹) →
      (∀ v ξ η, κ ≤ g v ξ η ∧ g v ξ η ≤ κ⁻¹) →
    ∀ (y : ℕ → ∀ v, Ys v) (x : ∀ v, Xs v) (n : ℕ) (k : ι) (J : Finset V), J ⊆ block blk k →
      IsProbabilityMeasure (bpfLaw ψ p g blk y x N n) ∧
      ∀ f : (∀ v, Xs v) → ℝ, IsTest (J : Set V) f →
        ∫⁻ a, ENNReal.ofReal ((∫ z, f z ∂(filt ψ p g y x n) -
            ∫ z, f z ∂(bpf g blk y x N n a)) ^ 2) ∂(bpfLaw ψ p g blk y x N n) ≤
          ENNReal.ofReal ((α ε κ r (maxNbhd G r) (maxBlockNbhd G r blk) * J.card *
            (decay (β₁ ε κ r (maxNbhd G r) (maxBlockNbhd G r blk))
                (setDist G J (innerBdry G r (block blk k))) +
              Real.exp (β₂ ε κ r (maxNbhd G r) (maxBlockNbhd G r blk) * maxBlock blk) /
                Real.sqrt N)) ^ 2) := by sorry

end LocalPF.Block
