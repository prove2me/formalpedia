-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_rich_weaklyMonotone_implementable
-- name    : MechanismDesign.IncentiveCompat.rich_weaklyMonotone_implementable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:12:38.453989+00:00
-- url     : https://prove2.me/theorems/e54684f6-0ffa-4624-9588-769815c22613
-- title:
--   Proposition 5.7 -- Bikhchandani et al.: weak monotonicity suffices on rich domains (finite A)
-- statement:
--   Suppose that the set $A$ of alternatives is finite and let $R$ be a reflexive and transitive, possibly incomplete, relation on $A$. Assume that
--
--   1. the type set is rich with respect to $R$: for every $v : A \to \mathbb R$ that represents $R$ ($aRb \Rightarrow v(a) \ge v(b)$) there is a type $\theta$ with $u(a,\theta) = v(a)$ for all $a \in A$; and
--   2. the type set is consistent with $R$: for every type $\theta$, the function $u(\cdot,\theta)$ represents $R$.
--
--   Then every weakly monotone decision rule $q$ is implementable: some $t : \Theta \to \mathbb R$ gives
--   $$u(q(\theta),\theta) - t(\theta) \ge u(q(\theta'),\theta) - t(\theta') \qquad \text{for all } \theta,\theta'.$$
--
--   With Proposition 5.1, weak monotonicity then characterizes implementability on such domains; this is Theorem 1 of Bikhchandani, Chatterji, Lavi, Mu'alem, Nisan and Sen (2006), which covers multi-object auctions with free disposal.
--
--   **Formalization Note** Condition 2 is part of Bikhchandani et al.'s rich-domain assumption (their domain is exactly the set of utility vectors consistent with the order) but is missing from the book's Definition 5.10. Without it the statement is false: take $A = \{a,b,c\}$, $R$ the total order $a \succeq b \succeq c$, and types $\Theta = \{\theta \in \mathbb R^3 : \theta_a \ge \theta_b \ge \theta_c\} \cup \{(0,1,0)\}$ with $u(x,\theta) = \theta_x$; the rule giving $c$ to $(0,1,0)$, $b$ to $(0,0,-1)$ and $a$ to every other type is weakly monotone but not implementable. Types need not be identified with their utility vectors (two types may share one).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.109, Proposition 5.7, Definition 5.10 (p.108); Bikhchandani, Chatterji, Lavi, Mu'alem, Nisan, Sen, Econometrica 74(4) (2006) 1109–1132, §3.1 rich-domain assumption and Theorem 1

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.7 (Bikhchandani et al. 2006, Theorem 1; p.109), in the corrected form: `A` is
finite, `R` is a reflexive and transitive relation on `A`, every `v : A → ℝ` representing `R` is
the utility function of some type (the book's Definition 5.10), and every type's utility function
represents `R` (the consistency of the domain in Bikhchandani et al., which the book's
definition omits and without which the statement is false). Then every weakly monotone decision
rule is implementable. -/
theorem rich_weaklyMonotone_implementable {A Θ : Type*} [Finite A] [Nonempty Θ]
    (u : A → Θ → ℝ) (R : A → A → Prop) (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c) (hrich : IsRichWRT u R)
    (hcons : IsConsistentWRT u R) (q : Θ → A) (hq : WeaklyMonotone u q) :
    Implementable u q := by sorry

end MechanismDesign.IncentiveCompat
