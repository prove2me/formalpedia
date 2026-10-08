-- Prove2me | Theorems.Thm_MechanismDesign_VCG_dsic_iff_monotone_one_dimensional
-- name    : MechanismDesign.VCG.dsic_iff_monotone_one_dimensional
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:17:27.429693+00:00
-- url     : https://prove2.me/theorems/8db34045-b2fb-4f97-af86-9c7140fd6a91
-- title:
--   Proposition 7.2 -- with one-dimensional bounded type sets, implementability iff monotonicity
-- statement:
--   In the dominant-strategy model of Chapter 7, suppose $A$ is finite. For every agent $i$ let $R_i$ be an order (a complete and transitive relation) of $A$, and suppose that every type set $\Theta_i$ is bounded and one-dimensional with respect to $R_i$ for agent $i$'s utility $u_i$. Let $q$ be a decision rule. Then
--
--   $$
--   \exists\, t_1, \dots, t_N \text{ such that } (q, t_1, \dots, t_N) \text{ is DSIC} \iff \text{for all } i \text{ and } \theta_{-i},\ \theta_i \mapsto q(\theta_i, \theta_{-i}) \text{ is monotone w.r.t. } R_i .
--   $$
--
--   Here $\theta_i \succ_{R_i} \theta_i'$ means that $\theta_i$ values every $R_i$-higher alternative strictly more, relative to every $R_i$-lower one, than $\theta_i'$ does (with zero utility difference between $R_i$-indifferent alternatives); one-dimensionality means that any two distinct types of agent $i$ are comparable in $\succ_{R_i}$; boundedness means there is $c > 0$ with $|u_i(a', \theta_i) - u_i(a, \theta_i)| < c$ for all $a, a', \theta_i$; and monotonicity with respect to $R_i$ means that $\theta_i \succ_{R_i} \theta_i'$ implies $q(\theta_i, \theta_{-i})\, R_i\, q(\theta_i', \theta_{-i})$.
--
--   This is the dominant-strategy version of Proposition 5.6: on one-dimensional domains, "higher types get higher alternatives" is exactly the implementability condition.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.132, Proposition 7.2 (with Definitions 5.6–5.9, pp.104–106)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.2 (p.132): suppose `A` is finite, for every agent `i` let `Rᵢ` be an
order (complete and transitive) of `A`, and suppose every type set `Θᵢ` is bounded and
one-dimensional with respect to `Rᵢ`. Then there are transfer rules making `(q, t₁, …, t_N)`
dominant strategy incentive-compatible if and only if, for every `i` and every `θ₋ᵢ`, the rule
`θᵢ ↦ q(θᵢ, θ₋ᵢ)` is monotone with respect to `Rᵢ`. -/
theorem dsic_iff_monotone_one_dimensional {ι A : Type*} {Θ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [Finite A] (u : ∀ i, A → Θ i → ℝ) (R : ι → A → A → Prop)
    (hR : ∀ i, IsCompleteOrder (R i)) (hbdd : ∀ i, BoundedTypes (u i))
    (h1d : ∀ i, OneDimensional (R i) (u i)) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j),
        MonotoneWRT (R i) (u i) (fun x : Θ i => q (Function.update θ i x)) := by sorry

end MechanismDesign.VCG
