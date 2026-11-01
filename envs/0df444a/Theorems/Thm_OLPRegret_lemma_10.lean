-- Prove2me | Theorems.Thm_OLPRegret_lemma_10
-- name    : OLPRegret.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:28.319865+00:00
-- url     : https://prove2.me/theorems/88f25730-a3cc-4705-9dbc-7814779ce683
-- title:
--   Lemma 10 — scaled shadow prices can sit near any $\gamma$
-- statement:
--   Under Assumptions 2–6, for all $\gamma\in\mathbb R^m$ and $\epsilon>0$ there are $\delta,C>0$ and $T$ such that for all $t\ge T$,
--   $$
--   P_*\Big(\forall b\in B_\delta(\beta),\ \forall y_t^b:\ \|\sqrt t(y_t^b-y_\infty^b)-\gamma\|\le\epsilon\Big)\ge C,
--   $$
--   over all minimizers $y_t^b$ of $\Lambda_t^b$.
--
--   The shadow price fluctuates by order $1/\sqrt t$ in every direction, which makes the per-period errors unavoidable.
--
--   Differences from the source:
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - reading: $\Pr$ of an event defined by a supremum over $b$ and minimizers → inner probability; reason: the event is not known to be measurable, and this is the strong direction of a lower bound
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 10, Online Appendix p.26 (PDF 62)

import Mathlib
import Definitions.Def_OLPRegret_dualMin
import Definitions.Def_OLPRegret_innerMeasure

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 10, Online Appendix p.26: for all `γ ∈ ℝᵐ` and `ε > 0` there exist
`δ, C > 0` such that `Pr(sup_{b ∈ B_δ(β)} ‖√t(yₜᵇ − y∞ᵇ) − γ‖ ≤ ε) ≥ C` for all sufficiently large `t`.

**Formalization Note** The event quantifies over all minimizers and its probability is an inner
probability. -/
theorem lemma_10 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) (γ : E m) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ t ≥ T,
      ENNReal.ofReal C ≤ innerMeasure (sampleLaw μ t)
        {s | ∀ b ∈ Metric.ball β δ, ∀ y ∈ dualMin s b,
          ‖Real.sqrt t • (y - yInf μ b) - γ‖ ≤ ε} := by sorry

end OLPRegret
