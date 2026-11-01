-- Prove2me | Theorems.Thm_OLPRegret_bellman_optimal
-- name    : OLPRegret.bellman_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:48.187624+00:00
-- url     : https://prove2.me/theorems/a557361b-c589-442f-831a-38052c24312a
-- title:
--   (12)–(15) — the Bellman policy is an optimal non-anticipating policy
-- statement:
--   Under Assumptions 2–6, let $W_t$ be the Bellman value and $\pi_t^b$ the optimal action. For every horizon $n$:
--
--   1. the realized decisions of the Bellman policy are those of a non-anticipating policy;
--   2. its expected online value is $\mathrm E(v_n^\beta)=W_n(\beta)$;
--   3. every non-anticipating policy has expected online value at most $W_n(\beta)$.
--
--   This ties the policy class of the mission's goal to the page's optimal policy.
--
--   Differences from the source:
--   - reading: "the expected-utility-maximizing policy", whose value satisfies (12)–(14) → the policy (14) lies in the non-anticipating class, has value $W_n(\beta)$, and no policy in the class does better; reason: the page states the Bellman equations without saying over which class the maximum is taken; this is the class of the mission
--   - encoding: ties in (14) unspecified; $x_ta_t\le tb$ a constraint → ties rejected ("exceeds", p.18); acceptance masked by feasibility; reason: ties do not change the value
--   - encoding: periods counted backward, $t=n,\dots,1$ → the index $t$ of `Fin n` holds period $t+1$, and the stock $tb_t$ is tracked with $b_t$ recovered by division; reason: Lean convention; same instances
-- source:
--   Bray, arXiv:1912.08917v6, (12)–(15), p.18

import Mathlib
import Definitions.Def_OLPRegret_bellmanValue
import Definitions.Def_OLPRegret_regret

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, (12)–(15), p.18: "Since you follow the expected-utility-maximizing
policy, this variable's expectation satisfies the following Bellman equations." The action (14) is
a non-anticipating policy, its expected online value is `E(vₙᵝ) = W n β`, and no non-anticipating
policy does better.

**Formalization Note** This is the item that ties "every non-anticipating policy" in
`OLPRegret.theorem_3` to the page's optimal policy. -/
theorem bellman_optimal {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) (n : ℕ) :
    (∃ π : Policy m n, ∀ ω t,
      decision π.scheme β ω t = decision (bellmanScheme μ) β ω t) ∧
    ∫ ω, onlineValue (bellmanScheme μ) β ω ∂sampleLaw μ n = W μ n β ∧
    ∀ π : Policy m n, ∫ ω, onlineValue π.scheme β ω ∂sampleLaw μ n ≤ W μ n β := by sorry

end OLPRegret
