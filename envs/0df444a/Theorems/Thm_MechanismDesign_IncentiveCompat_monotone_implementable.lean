-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_monotone_implementable
-- name    : MechanismDesign.IncentiveCompat.monotone_implementable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:12:39.220671+00:00
-- url     : https://prove2.me/theorems/d6908edc-72b0-4df8-8d18-5d511db4615a
-- title:
--   Proposition 5.6 -- on bounded one-dimensional type spaces with finite A, monotone decision rules are implementable
-- statement:
--   Suppose that the set $A$ of alternatives is finite, $R$ is a complete and transitive order of $A$, and the type set $\Theta$ is
--
--   1. bounded: there is $c > 0$ with $-c < u(a',\theta) - u(a,\theta) < c$ for all $a, a' \in A$ and $\theta \in \Theta$, and
--   2. one-dimensional with respect to $R$.
--
--   Then every decision rule $q$ that is monotone with respect to $R$ ($\theta \succ_R \theta' \Rightarrow q(\theta)\,R\,q(\theta')$) is implementable: there is $t : \Theta \to \mathbb R$ such that
--   $$u(q(\theta),\theta) - t(\theta) \ge u(q(\theta'),\theta) - t(\theta') \qquad \text{for all } \theta,\theta' \in \Theta.$$
--
--   Together with Propositions 5.1 and 5.5 this makes monotonicity necessary and sufficient for implementability on such domains, as in the one-dimensional models of Chapters 2–4.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.107, Proposition 5.6, Definition 5.9 (p.106)

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.6 (p.107): if `A` is finite, `R` is a complete and transitive order of `A`,
and `Θ` is bounded and one-dimensional with respect to `R`, then every decision rule that is
monotone with respect to `R` is implementable. -/
theorem monotone_implementable {A Θ : Type*} [Finite A] [Nonempty Θ] (u : A → Θ → ℝ)
    (R : A → A → Prop) (hR : IsCompleteTransitive R) (hbdd : IsBoundedTypeSpace u)
    (h1 : OneDimensional u R) (q : Θ → A) (hq : MonotoneWRT u R q) :
    Implementable u q := by sorry

end MechanismDesign.IncentiveCompat
