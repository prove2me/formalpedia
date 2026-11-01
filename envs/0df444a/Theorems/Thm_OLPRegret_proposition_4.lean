-- Prove2me | Theorems.Thm_OLPRegret_proposition_4
-- name    : OLPRegret.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:16.132719+00:00
-- url     : https://prove2.me/theorems/33a27032-c940-4052-a09a-156c4e21fcd8
-- title:
--   Proposition 4 — uniform $O(1/t)$ convergence of shadow prices
-- statement:
--   Under Assumptions 2–6, there are $\delta,C>0$ and $T$ such that for all $t\ge T$,
--   $$
--   \mathrm E^*\Big(\sup_{b\in B_\delta(\beta)}\ \sup_{y_t^b}\ \|y_t^b-y_\infty^b\|^2\Big)\le C/t,
--   $$
--   the inner supremum running over all minimizers of $\Lambda_t^b$.
--
--   Positioning the supremum inside the expectation is what lets the bound apply at the random inventory $b_t$.
--
--   Differences from the source:
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - reading: expectation of a supremum over $b$ and minimizers → outer expectation (infimum of $\int Z$ over measurable majorants $Z$); reason: the supremum is not known to be measurable; the paper derives these bounds from van der Vaart and Wellner, whose convention this is, and it is the strong direction
--   - encoding: $O(1/t)$ → $\exists C,T\ \forall t\ge T$; reason: asymptotic notation as $t\to\infty$; at small $t$ the left side can be infinite when $\mathrm E(u_1^2)=\infty$
-- source:
--   Bray, arXiv:1912.08917v6, Proposition 4, p.23

import Mathlib
import Definitions.Def_OLPRegret_dualMin
import Definitions.Def_PlugInRisk_outerExp

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Proposition 4, p.23: there exists `δ > 0` such that
`E(sup_{b ∈ B_δ(β)} ‖yₜᵇ − y∞ᵇ‖²) = O(1/t)`.

**Formalization Note** The supremum also runs over all minimizers `yₜᵇ`, and the expectation is an
outer expectation. `O(1/t)` is asymptotic: with only `E(u₁) < ∞`, the left side can be infinite at
small `t` (at `t = 1`, `y₁ᵇ` can equal `u₁/a₁`), so the threshold `T` is needed. -/
theorem proposition_4 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ t ≥ T,
      PlugInRisk.outerExp (sampleLaw μ t)
        (fun s => ⨆ b ∈ Metric.ball β δ, ⨆ y ∈ dualMin s b,
          ENNReal.ofReal (‖y - yInf μ b‖ ^ 2)) ≤ ENNReal.ofReal (C / t) := by sorry

end OLPRegret
