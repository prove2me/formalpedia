-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_maximal_badNormalizer_normalizer_eq_top
-- name    : OddOrder.Isaacs.Ch07.maximal_badNormalizer_normalizer_eq_top
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:07.74057+00:00
-- url     : https://prove2.me/theorems/5150231c-e78b-4e23-a3f3-f4bfc516f4b9
-- title:
--   Isaacs 7.1, Step 1: a bad $p$-subgroup of maximal normalizer $p$-part is normal
-- statement:
--   Say that $G$ satisfies the *Thompson local hypothesis at $p$* (`HasThompsonPComplementHypothesis p G`) if for every Sylow $p$-subgroup $P$ of $G$, both $C_G(Z(P))$ and $N_G(J(P))$ have a normal $p$-complement (`HasNormalPComplement`; a normal subgroup that complements every Sylow $p$-subgroup). Call a subgroup $U\le G$ *bad* (`IsBadNormalizerPSubgroup p U`) if $U\neq 1$, $U$ is a $p$-group, and $N_G(U)$ has no normal $p$-complement. For a subgroup $X$, let $w(X)$ (`normalizerPPart p X`) denote the $p$-part of $|N_G(X)|$, i.e. $p^{v_p(|N_G(X)|)}$.
--
--   Let $G$ be a finite group satisfying the Thompson local hypothesis at $p$, and assume the induction hypothesis: every finite group $H$ (same universe) with $|H|<|G|$ satisfying it has a normal $p$-complement. If $U$ is bad and $w(X)\le w(U)$ for every bad $X$, then
--   $$N_G(U)=G,$$
--   that is, $U\trianglelefteq G$.
--
--   This is the normalizer-growth part of Step 1 in the proof of Isaacs's Theorem 7.1.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L463-L579

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepOne

theorem maximal_badNormalizer_normalizer_eq_top.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U) :
    Subgroup.normalizer (U : Set G) = ⊤ := by sorry

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07
