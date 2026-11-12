-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_maximal_badNormalizer_eq_opCore
-- name    : OddOrder.Isaacs.Ch07.maximal_badNormalizer_eq_opCore
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:16.607409+00:00
-- url     : https://prove2.me/theorems/5bbac40b-4e77-4f60-81aa-2cc81ab76692
-- title:
--   Isaacs 7.1, Step 1: the maximal bad $p$-subgroup equals $O_p(G)$
-- statement:
--   Say that $G$ satisfies the *Thompson local hypothesis at $p$* (`HasThompsonPComplementHypothesis p G`) if for every Sylow $p$-subgroup $P$ of $G$, both $C_G(Z(P))$ and $N_G(J(P))$ have a normal $p$-complement (`HasNormalPComplement`; a normal subgroup that complements every Sylow $p$-subgroup). Call a subgroup $U\le G$ *bad* (`IsBadNormalizerPSubgroup p U`) if $U\neq 1$, $U$ is a $p$-group, and $N_G(U)$ has no normal $p$-complement. For a subgroup $X$, let $w(X)$ (`normalizerPPart p X`) denote the $p$-part of $|N_G(X)|$, i.e. $p^{v_p(|N_G(X)|)}$.
--
--   Let $G$ be a finite group satisfying the Thompson local hypothesis at $p$, with the induction hypothesis that every finite group $H$ (same universe) with $|H|<|G|$ satisfying it has a normal $p$-complement. Let $U$ be bad with $w(X)\le w(U)$ for every bad $X$, and $|X|\le|U|$ for every bad $X$ with $w(X)=w(U)$. Then
--   $$U=O_p(G).$$
--
--   This concludes Step 1 in the minimal-counterexample proof of Isaacs's Theorem 7.1.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L581-L633

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepOne

theorem maximal_badNormalizer_eq_opCore.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U)
    (hU_card_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) :
    U = OddOrder.Isaacs.Ch01.opCore p G := by sorry

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07
