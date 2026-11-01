-- Prove2me | Theorems.Thm_OLPRegret_lemma_8
-- name    : OLPRegret.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:53.92947+00:00
-- url     : https://prove2.me/theorems/4224d26a-45c6-4985-9a56-1e2ab928cc81
-- title:
--   Lemma 8 — the myopic regret of the optimal policy is $\Omega(1/t)$ (corrected: $m\ge1$)
-- statement:
--   Let $m\ge1$. Under Assumptions 2–6 and the Bellman policy, there is $\delta_0>0$ with $\delta_0\iota\le\beta$ such that for every $\delta\in(0,\delta_0]$ there are $C>0$ and $T$ with
--   $$
--   \mathrm E(r_t)\ge C/t\qquad\text{for all }n\text{ and all }t\ge T\text{ with }n^{3/4}\le t\le n/2,
--   $$
--   where $r_t$ is the lower myopic regret, for every choice of shadow prices. Summing over the range of $t$ gives $\Omega(\log n)$.
--
--   Differences from the source:
--   - correction: $m$ unrestricted → $1\le m$; reason: at $m=0$ every bundle is empty, $\Delta_t=u_t\ge0$ and the optimal policy accepts every $u_t>0$, so $r_t=0$
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - reading: $\mathrm E(r_t)$ for a possibly non-measurable $r_t$ → the lower integral `∫⁻`; reason: a non-measurable choice of minimizers is allowed, and the lower integral is the strong direction of a lower bound
--   - encoding: $\delta$ from (39), "small enough" → $\exists\delta_0\ \forall\delta\in(0,\delta_0]$; reason: Lemma 8's constant is for a fixed small $\delta$; the proof applies to each
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 8, p.32; proof Online Appendix pp.24–26 (PDF 60–62)

import Mathlib
import Definitions.Def_OLPRegret_bellmanValue
import Definitions.Def_OLPRegret_myopicRegret

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 8, p.32: under the optimal policy there exists `C > 0` such that
`E(rₜ) ≥ C/t`, for all sufficiently large `t` that satisfy `n^{3/4} ≤ t ≤ n/2`.

**Formalization Note** `rₜ` is `rLower` of (39), for `δ` small as in (39) (`δι ≤ β`). The bound holds
for every choice `Y` of shadow prices, with `∫⁻` the lower integral if the choice is not measurable.
`C` and the threshold depend on neither `n` nor `t`. At `m = 0` the left side is `0`, hence `1 ≤ m`. -/
theorem lemma_8 {m : ℕ} (hm : 1 ≤ m) (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ (∀ i, δ₀ ≤ β i) ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ (n : ℕ) (t : Fin n), T ≤ period t →
        (n : ℝ) ^ (3 / 4 : ℝ) ≤ (period t : ℕ) → ((period t : ℕ) : ℝ) ≤ n / 2 →
        ∀ Y : Sample m n → ℕ → E m → E m, (∀ ω, IsShadowPriceChoice ω (Y ω)) →
          ENNReal.ofReal (C / (period t : ℕ)) ≤
            ∫⁻ ω, ENNReal.ofReal (rLower δ (bellmanScheme μ) β (Y ω) ω t) ∂sampleLaw μ n := by sorry

end OLPRegret
