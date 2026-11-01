-- Prove2me | Theorems.Thm_OLPRegret_proposition_6
-- name    : OLPRegret.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:07.271102+00:00
-- url     : https://prove2.me/theorems/b093f0b7-3a7e-48e1-ac80-799a3f5c87ac
-- title:
--   Proposition 6 — exponential tails of shadow prices
-- statement:
--   Under Assumptions 2–6, for every $p\ge0$ there are $\delta,C>0$ and $\epsilon_0>0$ such that for every $\epsilon\in(0,\epsilon_0)$ and all sufficiently large $t$,
--   $$
--   \mathrm E^*\Big(\sup_{b\in B_\delta(\beta)}\ \sup_{y_t^b}\ \mathbb 1\{y_t^b\notin B_\epsilon(y_\infty^b)\}\|y_t^b-y_\infty^b\|^p\Big)\le\exp(-C\epsilon^2t),
--   $$
--   the inner supremum running over all minimizers of $\Lambda_t^b$.
--
--   Differences from the source:
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - reading: expectation of a supremum over $b$ and minimizers → outer expectation (infimum of $\int Z$ over measurable majorants $Z$); reason: the supremum is not known to be measurable; the paper derives these bounds from van der Vaart and Wellner, whose convention this is, and it is the strong direction
--   - reading: "for all sufficiently small $\epsilon>0$ and sufficiently large $t$" → $\exists\epsilon_0\ \forall\epsilon\in(0,\epsilon_0)\ \exists T\ \forall t\ge T$; reason: the threshold may depend on $\epsilon$; a uniform threshold looks false for $m\ge3$ by a CLT heuristic, and Lemma 4 uses a fixed $\epsilon$
--   - encoding: $\|\cdot\|^p$ at $p=0$ → real power with $\|\cdot\|^0=1$; reason: gives Corollary 3, p.24
-- source:
--   Bray, arXiv:1912.08917v6, Proposition 6, p.24

import Mathlib
import Definitions.Def_OLPRegret_dualMin
import Definitions.Def_PlugInRisk_outerExp

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Proposition 6, p.24: for all `p ≥ 0`, there exist `δ, C > 0` such that
`E(sup_{b ∈ B_δ(β)} 𝟙{yₜᵇ ∉ B_ε(y∞ᵇ)}‖yₜᵇ − y∞ᵇ‖ᵖ) ≤ exp(−Cε²t)` for all sufficiently small `ε > 0` and
sufficiently large `t`.

**Formalization Note** The supremum also runs over all minimizers, and the expectation is an outer
expectation. "Sufficiently large `t`" may depend on `ε`. At `p = 0`, `‖·‖⁰ = 1`, which gives
Corollary 3, p.24. -/
theorem proposition_6 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) (p : ℝ) (hp : 0 ≤ p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ T : ℕ, ∀ t ≥ T,
        PlugInRisk.outerExp (sampleLaw μ t)
          (fun s => ⨆ b ∈ Metric.ball β δ, ⨆ y ∈ dualMin s b,
            (Metric.ball (yInf μ b) ε)ᶜ.indicator
              (fun y' => ENNReal.ofReal (‖y' - yInf μ b‖ ^ p)) y) ≤
          ENNReal.ofReal (Real.exp (-C * ε ^ 2 * t)) := by sorry

end OLPRegret
