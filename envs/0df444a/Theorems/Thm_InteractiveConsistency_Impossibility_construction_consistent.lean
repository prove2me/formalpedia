-- Prove2me | Theorems.Thm_InteractiveConsistency_Impossibility_construction_consistent
-- name    : InteractiveConsistency.Impossibility.construction_consistent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:56.586535+00:00
-- url     : https://prove2.me/theorems/e1796bec-2425-4376-ae78-7b607132bf8e
-- title:
--   Section 4, proof (p. 233) — α, β, σ are consistent with A ∪ C, B ∪ C, A ∪ B, respectively
-- statement:
--   Let $A$, $B$, $C$ be pairwise disjoint sets with $A\cup B\cup C=P$, let $v, v'\in V$, and let $\alpha$, $\beta$, $\sigma$ be the scenarios defined by (i)–(iii) of p. 232. Then
--
--   1. $\alpha$ is consistent with $N = A\cup C$;
--   2. $\beta$ is consistent with $N = B\cup C$;
--   3. $\sigma$ is consistent with $N = A\cup B$.
--
--   That is, for instance, $\alpha(pqw)=\alpha(qw)$ for all $q\in A\cup C$, $p\in P$ and $w\in P^*$. Each of the three scenarios is therefore a legitimate behaviour of a system whose faulty processors are $B$, $A$, $C$ respectively.
--
--   **Formalization Note** The page asserts this "by inspection"; the statement does not need $A$, $B$, $C$ to be nonempty, nor $v\ne v'$, so those hypotheses of the surrounding proof are omitted.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 233, Section 4, proof of the THEOREM, first sentence

import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario
import Definitions.Def_InteractiveConsistency_Impossibility_Construction

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, proof of the THEOREM, p. 233: for a partition
`A, B, C` of `P` and any values `v, v'`, the scenarios `α`, `β`, `σ` defined by (i)–(iii) of p. 232
are consistent with `N = A ∪ C`, `B ∪ C`, `A ∪ B`, respectively. -/
theorem construction_consistent {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hP : A ∪ B ∪ C = P) :
    ConsistentWith P (A ∪ C) (alphaScen P A B C v v') ∧
    ConsistentWith P (B ∪ C) (betaScen P A B C v v') ∧
    ConsistentWith P (A ∪ B) (sigmaScen P A B C v v') := by sorry

end InteractiveConsistency.Impossibility
