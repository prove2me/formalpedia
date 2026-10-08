-- Prove2me | Theorems.Thm_MechanismDesign_VCG_weakly_monotone_pad
-- name    : MechanismDesign.VCG.weakly_monotone_pad
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:17:48.278199+00:00
-- url     : https://prove2.me/theorems/706b9e73-37df-407a-b8ef-728d439e3d26
-- title:
--   Proposition 7.5 -- weak monotonicity in every agent's type implies positive association of differences
-- statement:
--   In the dominant-strategy model of Chapter 7, let $q$ be a decision rule that is weakly monotone in every $\theta_i$: for every agent $i$, every $\theta_{-i}$ and all types $\theta_i, \theta_i'$ of agent $i$, writing $a = q(\theta_i, \theta_{-i})$ and $b = q(\theta_i', \theta_{-i})$,
--
--   $$
--   u_i(a, \theta_i) - u_i(b, \theta_i) \ge u_i(a, \theta_i') - u_i(b, \theta_i') .
--   $$
--
--   Then $q$ satisfies positive association of differences: if $q(\theta) = a$ and $u_i(a, \theta_i') - u_i(b, \theta_i') > u_i(a, \theta_i) - u_i(b, \theta_i)$ for every agent $i$ and every $b \ne a$, then $q(\theta') = a$.
--
--   Since dominant-strategy implementable rules are weakly monotone in every agent's type (Proposition 5.1 applied agent by agent), PAD is a necessary condition for dominant-strategy implementability.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.135, Proposition 7.5 (with Definition 5.4, p.97)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.5 (p.135): if `q` is weakly monotone in every `θᵢ` (for every agent
`i` and every `θ₋ᵢ`, the rule `θᵢ ↦ q(θᵢ, θ₋ᵢ)` is weakly monotone in the sense of
Definition 5.4 for agent `i`'s utility), then `q` satisfies positive association of differences. -/
theorem weakly_monotone_pad {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) (hq : WeaklyMonotoneInEvery u q) :
    PAD u q := by sorry

end MechanismDesign.VCG
