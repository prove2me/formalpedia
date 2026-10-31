-- Prove2me | Theorems.Thm_LSAPR_lemma_7
-- name    : LSAPR.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:01.991807+00:00
-- url     : https://prove2.me/theorems/285a9c8a-9e53-4a4e-8329-79e9719706b0
-- title:
--   Lemma 7 — a sub-Gaussian tail gives $\mathbb E[\|X\|^p]\le2p^{p/2}\sigma^p$
-- statement:
--   Let $X$ be an $\mathbb R^d$-valued random variable and $\sigma^2>0$ with
--   $$\mathbb P(\|X\|\ge t)\le2\exp\big(-t^2/(2\sigma^2)\big)\quad\text{for all }t\ge0.$$
--   Then for every real $p\ge2$,
--   $$\mathbb E[\|X\|^p]\le2p^{p/2}\sigma^p.$$
--
--   Combined with Lemma 8, this converts concentration of linear statistics into moment bounds of order $\sqrt p$.
--
--   Differences from the source:
--   - encoding: E[‖X‖^p] → the lower Lebesgue integral ∫⁻ ‖X‖ₑ^p in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound
--   - encoding: some σ² > 0 → σ > 0; reason: the conclusion uses σ^p, the positive root of σ²
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Lemma 7, p.35

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- Lemma 7, arXiv:2207.04475v2, p.35: an `ℝ^d`-valued random variable with the sub-Gaussian tail
`P(‖X‖ ≥ t) ≤ 2 exp(-t² / (2σ²))` for all `t ≥ 0`, where `σ² > 0`, satisfies
`E[‖X‖^p] ≤ 2 p^{p/2} σ^p` for every real `p ≥ 2`.

**Formalization Note.** `E[‖X‖^p]` is a lower Lebesgue integral in `ℝ≥0∞`, so an infinite moment
would falsify the bound. -/
theorem lemma_7 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → Vec d) (hX : Measurable X) (σ : ℝ) (hσ : 0 < σ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ ‖X ω‖} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2))))
    (p : ℝ) (hp : 2 ≤ p) :
    ∫⁻ ω, ‖X ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal (2 * p ^ (p / 2) * σ ^ p) := by sorry

end LSAPR
