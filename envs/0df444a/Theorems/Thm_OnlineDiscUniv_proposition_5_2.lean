-- Prove2me | Theorems.Thm_OnlineDiscUniv_proposition_5_2
-- name    : OnlineDiscUniv.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:00.904121+00:00
-- url     : https://prove2.me/theorems/84c371a0-ff4b-4951-9fdd-e9969a5bd726
-- title:
--   Proposition 5.2 — infeasibility below the Brownian value: $\sup_{\varepsilon}\mathbb P(D_{M,N}\le\kappa)\to0$ for $0\le\kappa<R_\alpha$
-- statement:
--   Suppose $\mu$ has mean zero, unit variance and a finite fourth moment. For every $0\le\kappa<R_\alpha$ and every sequence $M/N\to\alpha$,
--   $$
--   \sup_{\varepsilon\text{ online}}\mathbb P(D_{M,N}\le\kappa)\longrightarrow0.\qquad(5.5)
--   $$
--
--   This is clause (ii) of Theorem 1.1: no online algorithm, randomized or not, keeps all $M$ constraints below $R_\alpha$ with probability bounded away from zero.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - reading: inf / sup over randomized online algorithms (seed space unspecified) → inf / sup over every seed space S : Type with a σ-algebra, every seed probability law and every jointly measurable causal sign map; reason: the paper fixes no seed space; quantifying over all of them is the stronger reading of both the lower and the upper bound
--   - encoding: ε_k = A_{k,M,N}(U, ξ_1, …, ξ_k) ∈ {−1,+1} → sign maps jointly measurable in (seed, input), constant in columns after k; reason: measurability is implicit in the paper (probabilities and expectations of D_{M,N} must be defined); causality is the online constraint
--   - encoding: µ has mean zero, variance one and a finite fourth moment → IsProbabilityMeasure µ, Integrable x⁴, ∫ x dµ = 0, ∫ x² dµ = 1; reason: x⁴ integrable implies x and x² integrable for a probability law, so the Bochner integrals are the true moments
--   - encoding: M/N → α (M = M_N) → every integer sequence Mseq with Mseq N / N → α; reason: the paper's standing convention of §2.1
--   - encoding: R_α and the probabilities real-valued (possibly infinite) → values in ℝ≥0∞, real bounds embedded by ENNReal.ofReal; reason: the same inequalities and limits; avoids junk values of sInf ∅ and toReal ⊤
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Proposition 5.2, (5.5), p.24 (PDF p.25)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha
import Definitions.Def_OnlineDiscUniv_optDisc

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Proposition 5.2** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.24,
PDF p.25). Suppose `μ` has mean zero, unit variance, and a finite fourth moment. For every
`0 ≤ κ < R_α` and every sequence `M/N → α`, `sup_{ε online} P(D_{M,N} ≤ κ) → 0` (5.5).

**Formalization Note** `M = M_N` is any integer sequence with `M_N/N → α > 0` (§2.1). The
supremum is over every seed space, seed law and (measurable, causal) online algorithm
(`optSucc`). "Finite fourth moment" is integrability of `x⁴`, which gives integrability of `x` and
`x²` for a probability law. -/
theorem proposition_5_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (α : ℝ) (hα : 0 < α)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h4 : Integrable (fun x : ℝ => x ^ 4) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ENNReal.ofReal κ < Ralpha P B α) (Mseq : ℕ → ℕ)
    (hM : Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => optSucc μ (Mseq N) N κ) atTop (𝓝 0) := by sorry

end OnlineDiscUniv
