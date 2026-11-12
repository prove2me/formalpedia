-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_HasThompsonLocalPComplements_of_subgroup
-- name    : OddOrder.Isaacs.Ch07.HasThompsonLocalPComplements.of_subgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:15.505038+00:00
-- url     : https://prove2.me/theorems/b189341f-3ada-4abc-b866-a115b68ab219
-- title:
--   Thompson local normal-complement hypotheses descend to a subgroup
-- statement:
--   Let $G$ be a finite group, $p$ a prime, $H\le G$ a subgroup and $S\le H$ a subgroup of the group $H$. For a subgroup $Q$ of a group $X$ write $\mathrm{TL}_p(Q)$ for the conjunction: $C_X(Z(Q))$ has a normal $p$-complement and $N_X(J(Q))$ has a normal $p$-complement (`HasThompsonLocalPComplements p Q`). If $\mathrm{TL}_p$ holds for the image of $S$ in $G$ (`S.map H.subtype`, computed in $G$), then $\mathrm{TL}_p(S)$ holds computed inside $H$.
--
--   It lets the Thompson local hypotheses of Isaacs's Theorem 7.1 be passed to subgroups containing a given $p$-subgroup.
--
--   **Formalization Note.** `HasNormalPComplement p X` means there is a normal subgroup of $X$ that complements every Sylow $p$-subgroup of $X$. No hypothesis on $S$ being a $p$-group is made.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L190-L230

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section LocalHypothesisTransport

theorem HasThompsonLocalPComplements.of_subgroup
    [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    {S : Subgroup H}
    (hS : HasThompsonLocalPComplements p (S.map H.subtype)) :
    HasThompsonLocalPComplements p S := by sorry

end LocalHypothesisTransport

end OddOrder.Isaacs.Ch07
