-- Prove2me | Theorems.Thm_InteractiveConsistency_Impossibility_construction_indistinguishable
-- name    : InteractiveConsistency.Impossibility.construction_indistinguishable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:53.117977+00:00
-- url     : https://prove2.me/theorems/a53229e7-a8ac-4ecd-b790-f5efb7aa8d20
-- title:
--   Section 4, proof (p. 233) — α(aw) = σ(aw) and β(bw) = σ(bw) for all a ∈ A, b ∈ B, w ∈ P*
-- statement:
--   Let $A$, $B$, $C$ be pairwise disjoint sets with $A\cup B\cup C=P$, let $v, v'\in V$, and let $\alpha$, $\beta$, $\sigma$ be the scenarios defined by (i)–(iii) of p. 232. Then
--   $$\alpha(aw)=\sigma(aw),\qquad \beta(bw)=\sigma(bw)$$
--   for all $a\in A$, $b\in B$ and $w\in P^*$. Equivalently, $\alpha_a=\sigma_a$ and $\beta_b=\sigma_b$: no processor of $A$ can distinguish $\alpha$ from $\sigma$, and no processor of $B$ can distinguish $\beta$ from $\sigma$.
--
--   This is what turns the three consistent scenarios into a contradiction with interactive consistency: a processor's decision depends only on its own $p$-scenario.
--
--   **Formalization Note** Scenarios are total functions on lists; the statement is the equality of the restrictions $w\mapsto\alpha(aw)$ and $w\mapsto\sigma(aw)$ as functions, which on strings over $P$ is the page's identity and on the remaining lists holds because all three scenarios take the same value $v$ there.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 233, Section 4, proof of the THEOREM, second sentence

import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario
import Definitions.Def_InteractiveConsistency_Impossibility_Construction

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, proof of the THEOREM, p. 233: for a partition
`A, B, C` of `P` and any values `v, v'`, the scenarios of p. 232 satisfy `α(aw) = σ(aw)` and
`β(bw) = σ(bw)` for all `a ∈ A`, `b ∈ B` and strings `w`; that is, `α_a = σ_a` and `β_b = σ_b`
as `a`- and `b`-scenarios. -/
theorem construction_indistinguishable {α V : Type*} [DecidableEq α] (P A B C : Finset α)
    (v v' : V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hP : A ∪ B ∪ C = P) :
    (∀ a ∈ A, restrict (alphaScen P A B C v v') a = restrict (sigmaScen P A B C v v') a) ∧
    (∀ b ∈ B, restrict (betaScen P A B C v v') b = restrict (sigmaScen P A B C v v') b) := by sorry

end InteractiveConsistency.Impossibility
