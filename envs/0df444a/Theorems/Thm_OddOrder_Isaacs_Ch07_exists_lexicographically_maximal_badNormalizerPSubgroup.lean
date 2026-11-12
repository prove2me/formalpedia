-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_exists_lexicographically_maximal_badNormalizerPSubgroup
-- name    : OddOrder.Isaacs.Ch07.exists_lexicographically_maximal_badNormalizerPSubgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:26.837035+00:00
-- url     : https://prove2.me/theorems/7ef367af-e2de-431e-850d-085f6f096005
-- title:
--   Isaacs 7.1, Step 1: a bad $p$-subgroup maximizing the $p$-part of $|N_G(U)|$, then $|U|$
-- statement:
--   Call a subgroup $U\le G$ *bad* (`IsBadNormalizerPSubgroup p U`) if $U\neq 1$, $U$ is a $p$-group, and $N_G(U)$ has no normal $p$-complement. For a subgroup $X$, let $w(X)$ (`normalizerPPart p X`) denote the $p$-part of $|N_G(X)|$, i.e. $p^{v_p(|N_G(X)|)}$.
--
--   Let $G$ be a finite group and $p$ a prime, and suppose $G$ has no normal $p$-complement. Then there exists a bad subgroup $U$ such that
--   $$w(X)\le w(U)\ \text{ for every bad } X,\qquad\text{and}\qquad |X|\le |U|\ \text{ for every bad } X \text{ with } w(X)=w(U).$$
--
--   This is the lexicographic choice of $U$ in Step 1 of the minimal-counterexample argument for Isaacs's Theorem 7.1; $U$ is then shown to be $O_p(G)$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L416-L462

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepOne

theorem exists_lexicographically_maximal_badNormalizerPSubgroup
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    ∃ U : Subgroup G,
      IsBadNormalizerPSubgroup p U ∧
      (∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
        normalizerPPart p X ≤ normalizerPPart p U) ∧
      (∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
        normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) := by sorry

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07
