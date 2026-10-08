-- Prove2me | Theorems.Thm_KelsoCrawford_NoCore_firm_j_subadditive_not_gs
-- name    : KelsoCrawford.NoCore.firm_j_subadditive_not_gs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:22.73269+00:00
-- url     : https://prove2.me/theorems/cc740780-f353-4c55-b4fe-d4a5e43d00b7
-- title:
--   Section 6, p. 1502 — firm j's technology is subadditive and satisfies (MP) and (NFL), but (GS) fails
-- statement:
--   Let $y^j$ be firm $j$'s technology from the example of Section 6, with reservation salaries $\sigma_{ij} = 0$ for $i = 1, 2, 3$. Then
--
--   1. $y^j$ is subadditive: $y^j(A \cup B) \le y^j(A) + y^j(B)$ for disjoint $A, B$;
--   2. (MP) holds for firm $j$: $y^j(C \cup \{i\}) - y^j(C) - \sigma_{ij} \ge 0$ for every worker $i$ and every $C \not\ni i$;
--   3. (NFL) holds for firm $j$: $y^j(\emptyset) = 0$;
--   4. (GS) fails for firm $j$ when salaries vary continuously: there are salary vectors $s^j \le \tilde s^j$ and a demanded set $C \in M^j(s^j)$ such that no demanded set at $\tilde s^j$ contains all workers of $C$ whose salary is unchanged.
--
--   The example shows that, with three or more workers, subadditivity of a firm's technology does not imply (GS), in contrast with the two-worker case.
--
--   **Formalization Note** The sentence on p. 1502 concerns firm $j$ alone, so (MP) and (NFL) are stated for firm $j$'s technology and $\sigma_{ij}$; the reservation salaries are read from the example market, where they are $0$. (GS) is negated on the set of all real salary vectors.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1502, Section 6

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Notions
import Definitions.Def_KelsoCrawford_NoCore_Example

namespace KelsoCrawford.NoCore

theorem firm_j_subadditive_not_gs :
    KelsoCrawford.Returns.Subadditive techJ ∧
    (∀ (i : Fin 3) (C : Finset (Fin 3)), i ∉ C →
      0 ≤ techJ (insert i C) - techJ C - noCoreMarket.σ i 0) ∧
    techJ ∅ = 0 ∧
    ¬ KelsoCrawford.Process.GrossSubstitutesOn techJ Set.univ := by sorry

end KelsoCrawford.NoCore
