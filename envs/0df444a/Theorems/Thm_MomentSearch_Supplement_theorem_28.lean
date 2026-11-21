-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_28
-- name    : MomentSearch.Supplement.theorem_28
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T09:37:05.976043+00:00
-- url     : https://prove2.me/theorems/b298f5c9-2ada-42b5-aacc-dc04e270ed47
-- title:
--   Theorem 28 — randomized sketches of $\tfrac12 n^{\varepsilon}\log n$ bits with randomized search rules still lose a factor $\gamma_{\mathrm{rand}}/\varepsilon$
-- statement:
--   There is a universal constant $\gamma_{\mathrm{rand}}>0$ such that for every fixed $\varepsilon\in(0,1/4)$ there exists $n_0(\varepsilon)$ with the following property for all $n\ge n_0(\varepsilon)$. Let $R$ be a random seed on a probability space $(\Omega,\mu)$, independent of the input distribution and of the target. For every seed $r$ let $\sigma_r:\Delta_n\to\{0,1\}^k$ be a sketch with $k\le\tfrac12 n^{\varepsilon}\log_2 n$ and let $S_r(x)$ be the correct deterministic search strategy chosen on message $x$. Then there is a distribution $p\in\Delta_n$ with
--   $$\mathbb E_R\big[\mathrm{cost}_p\big(S_R(\sigma_R(p))\big)\big]\ge\frac{\gamma_{\mathrm{rand}}}{\varepsilon}\,\mathrm{OPT}(p).$$
--
--   The information-theoretic lower bound of Theorem 6 therefore survives randomization of both the sketch and the search rule; the comparator $\mathrm{OPT}(p)$ is unchanged.
--
--   Differences from the source:
--   - encoding: E_R[cost_p(S_R(σ_R(p)))] for a random seed R → the Bochner integral ∫ cost_p(S_r(σ_r(p))) dμ(r) over a probability space (Ω, μ), Ω : Type, under the hypothesis that r ↦ cost_p(S_r(σ_r(p))) is measurable for every p ∈ Δ_n; reason: the hypothesis only makes E_R defined; the cost is bounded, so a measurable cost is integrable and the integral is the expectation
--   - encoding: σ_r : Δ_n → {0,1}^k and S_r(x) a correct deterministic strategy → σ : Ω → (Fin n → ℝ) → (Fin k → Bool) and S : Ω → (Fin k → Bool) → Strategy n; reason: only values on Δ_n are used; the published Strategy type contains exactly the correct deterministic strategies
--   - reading: γ_rand > 0 is a universal constant → ∃ γ > 0 chosen before ε, n₀ and n; reason: universal means independent of ε, n, k and the randomized pair; only n₀ depends on ε
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 28, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_MomentSearch_OPT

namespace MomentSearch.Supplement

open MomentSearch MeasureTheory

/-- **Theorem 28** (Randomized information-theoretic lower bound) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 28, p.36
(PDF p.38)).

There is a universal constant `γ_rand > 0` such that for every fixed `ε ∈ (0, 1/4)` there is
`n₀(ε)` with the following property for all `n ≥ n₀(ε)`. Let `R` be a random seed on a
probability space `(Ω, μ)`, independent of the input distribution and the target; for each seed
`r` let `σ_r : Δ_n → {0,1}^k` be a sketch with `k ≤ ½ n^ε log₂ n`, and `S_r(x)` the correct
deterministic search strategy chosen on message `x`. Then some distribution `p ∈ Δ_n` satisfies
`E_R[cost_p(S_R(σ_R(p)))] ≥ (γ_rand/ε) · OPT(p)`.

**Formalization Note.** `E_R` is the Bochner integral over `μ`. The hypothesis that
`r ↦ cost_p(S_r(σ_r(p)))` is measurable for every `p ∈ Δ_n` only makes the expectation defined: the
cost is bounded (by `n` times the depth of a tree on `n` vertices), so a measurable cost is
integrable. `p` is chosen after the randomized pair `(σ, S)` and does not depend on the seed.
Strategies are the published `MomentSearch.Strategy` (correct by construction). -/
theorem theorem_28 :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ (k : ℕ), (k : ℝ) ≤ 1 / 2 * (n : ℝ) ^ ε * Real.logb 2 n →
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (σ : Ω → (Fin n → ℝ) → (Fin k → Bool)) (S : Ω → (Fin k → Bool) → Strategy n),
            (∀ p ∈ stdSimplex ℝ (Fin n), Measurable (fun r => cost p (S r (σ r p)))) →
            ∃ p ∈ stdSimplex ℝ (Fin n),
              γ / ε * OPT p ≤ ∫ r, cost p (S r (σ r p)) ∂μ := by sorry

end MomentSearch.Supplement
