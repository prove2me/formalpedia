-- Prove2me | Theorems.Thm_OnlineDiscUniv_theorem_1_1
-- name    : OnlineDiscUniv.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:20.239358+00:00
-- url     : https://prove2.me/theorems/2985b92c-31df-4338-8072-0169a45cb732
-- title:
--   Theorem 1.1 (Universality of online discrepancy) — $\inf_{\varepsilon\text{ online}}\mathbb E_\mu D_{M,N}\to R_\alpha$ for every entry law with a finite fourth moment
-- statement:
--   Fix $\alpha>0$ and let $M/N\to\alpha$. If $\mu$ has mean zero, variance one and a finite fourth moment, then
--   $$
--   \inf_{\varepsilon\text{ online}}\mathbb E_\mu D_{M,N}\longrightarrow R_\alpha=\sqrt\alpha\,V^\infty_{1/\alpha}.
--   $$
--   Moreover:
--
--   1. For every fixed $\kappa>R_\alpha$ and $K<\infty$, there is a randomized online algorithm, depending only on $(\alpha,\kappa,K)$, such that for every centered law $\mu$ with variance one and $\mathbb E_\mu|\xi|^4\le K$,
--   $$
--   \mathbb P_\mu(D_{M,N}>\kappa)+\mathbb E_\mu(D_{M,N}-\kappa)_+\longrightarrow0 .
--   $$
--   2. For every fixed $\kappa<R_\alpha$,
--   $$
--   \sup_{\varepsilon\text{ online}}\mathbb P_\mu(D_{M,N}\le\kappa)\longrightarrow0 .
--   $$
--
--   The limit does not depend on $\mu$: Rademacher entries have the same optimal online discrepancy as Gaussian ones.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - reading: inf / sup over randomized online algorithms (seed space unspecified) → inf / sup over every seed space S : Type with a σ-algebra, every seed probability law and every jointly measurable causal sign map; reason: the paper fixes no seed space; quantifying over all of them is the stronger reading of both the lower and the upper bound
--   - encoding: ε_k = A_{k,M,N}(U, ξ_1, …, ξ_k) ∈ {−1,+1} → sign maps jointly measurable in (seed, input), constant in columns after k; reason: measurability is implicit in the paper (probabilities and expectations of D_{M,N} must be defined); causality is the online constraint
--   - encoding: µ has mean zero, variance one and a finite fourth moment → IsProbabilityMeasure µ, Integrable x⁴, ∫ x dµ = 0, ∫ x² dµ = 1; reason: x⁴ integrable implies x and x² integrable for a probability law, so the Bochner integrals are the true moments
--   - encoding: M/N → α (M = M_N) → every integer sequence Mseq with Mseq N / N → α; reason: the paper's standing convention of §2.1
--   - reading: (i) a randomized online algorithm depending only on (α, κ, K) → a family alg M N with seed unitInterval under Lebesgue measure, chosen before µ ∈ M_4(K) and before the sequence M_N; convergence for each µ and each sequence; reason: the paper's Algorithm 1 is defined for every (M, N); a specific seed space is stronger than an unspecified one; the convergence in (i) is per law, as stated
--   - encoding: κ > R_α, κ < R_α for real κ; limits, probabilities and expectations → R_α < ofReal κ; κ < 0 ∨ ofReal κ < R_α; values and limits in ℝ≥0∞; reason: exactly the order between a real κ and R_α ∈ [0, ∞]; no finiteness of R_α is assumed
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Theorem 1.1, pp.1–2 (PDF pp.2–3)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha
import Definitions.Def_OnlineDiscUniv_MomentClass
import Definitions.Def_OnlineDiscUniv_optDisc

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Theorem 1.1 (Universality of online discrepancy)** (Jo–Lee, *Exact Universality of Online
Discrepancy*, arXiv:2610.00103, artifact sha256 cb190f12…, printed pp.1–2, PDF pp.2–3). Fix `α > 0`
and let `M/N → α`. If `μ` has mean zero, variance one, and a finite fourth moment, then
`inf_{ε online} E_μ D_{M,N} → R_α`. Moreover:
(i) for every fixed `κ > R_α` and `K < ∞`, there is a randomized online algorithm, depending only
on `(α, κ, K)`, such that for every centered law `μ` with variance one and `E_μ|ξ|⁴ ≤ K`,
`P_μ(D_{M,N} > κ) + E_μ(D_{M,N} − κ)_+ → 0`;
(ii) for every fixed `κ < R_α`, `sup_{ε online} P_μ(D_{M,N} ≤ κ) → 0`.

**Formalization Note** `R_α = √α V^∞_{1/α}` is computed from an arbitrary standard Brownian motion
`B` on an arbitrary probability space (it depends only on the law of `B`). `M = M_N` is any integer
sequence with `M_N/N → α`. The infimum (`optDisc`) and supremum (`optSucc`) range over every seed
space `S : Type`, seed law and jointly measurable causal online algorithm. In (i) the algorithm is a
family `alg M N` with seed `unitInterval` under Lebesgue measure, chosen before `μ` and before the
sequence `M_N`; convergence is for each `μ` and each sequence. In (ii), `κ < R_α` for a real `κ` and
`R_α ∈ ℝ≥0∞` is written `κ < 0 ∨ ofReal κ < R_α`; in (i), `κ > R_α` is `R_α < ofReal κ`. All values are in `ℝ≥0∞`; no finiteness of `R_α` is assumed.
"Finite fourth moment" is integrability of `x⁴`. -/
theorem theorem_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (α : ℝ) (hα : 0 < α) :
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (fun x : ℝ => x ^ 4) μ →
      ∫ x, x ∂μ = 0 → ∫ x, x ^ 2 ∂μ = 1 →
      ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
        Tendsto (fun N : ℕ => optDisc μ (Mseq N) N) atTop (𝓝 (Ralpha P B α))) ∧
    (∀ κ : ℝ, Ralpha P B α < ENNReal.ofReal κ → ∀ K : ℝ,
      ∃ alg : (M N : ℕ) → OnlineAlg unitInterval M N, ∀ μ ∈ MomentClass 4 K,
        ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
          Tendsto (fun N : ℕ =>
            failProb μ (volume : Measure unitInterval) (alg (Mseq N) N) κ +
              expExcess μ (volume : Measure unitInterval) (alg (Mseq N) N) κ)
            atTop (𝓝 0)) ∧
    (∀ κ : ℝ, κ < 0 ∨ ENNReal.ofReal κ < Ralpha P B α →
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (fun x : ℝ => x ^ 4) μ →
        ∫ x, x ∂μ = 0 → ∫ x, x ^ 2 ∂μ = 1 →
        ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
          Tendsto (fun N : ℕ => optSucc μ (Mseq N) N κ) atTop (𝓝 0)) := by sorry

end OnlineDiscUniv
