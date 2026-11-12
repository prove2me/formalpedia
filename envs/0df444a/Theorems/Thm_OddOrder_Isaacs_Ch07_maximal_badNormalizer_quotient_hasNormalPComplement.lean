-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_maximal_badNormalizer_quotient_hasNormalPComplement
-- name    : OddOrder.Isaacs.Ch07.maximal_badNormalizer_quotient_hasNormalPComplement
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:27.220589+00:00
-- url     : https://prove2.me/theorems/8c6a7e3b-6d54-44c8-89eb-41d998b15172
-- title:
--   Isaacs 7.1, Step 2: $G/U$ has a normal $p$-complement for maximal bad $U$
-- statement:
--   Say that $G$ satisfies the *Thompson local hypothesis at $p$* (`HasThompsonPComplementHypothesis p G`) if for every Sylow $p$-subgroup $P$ of $G$, both $C_G(Z(P))$ and $N_G(J(P))$ have a normal $p$-complement (`HasNormalPComplement`; a normal subgroup that complements every Sylow $p$-subgroup). Call a subgroup $U\le G$ *bad* (`IsBadNormalizerPSubgroup p U`) if $U\neq 1$, $U$ is a $p$-group, and $N_G(U)$ has no normal $p$-complement. For a subgroup $X$, let $w(X)$ (`normalizerPPart p X`) denote the $p$-part of $|N_G(X)|$, i.e. $p^{v_p(|N_G(X)|)}$.
--
--   Let $G$ be a finite group and $p$ a prime. Assume the induction hypothesis: every finite group $H$ (same universe) with $|H|<|G|$ satisfying the Thompson local hypothesis at $p$ has a normal $p$-complement. Let $U\trianglelefteq G$ be a normal bad subgroup with $w(X)\le w(U)$ for every bad $X$, and $|X|\le|U|$ for every bad $X$ with $w(X)=w(U)$. Then
--   $$G/U\ \text{has a normal } p\text{-complement.}$$
--
--   This is Step 2 in the proof of Isaacs's Theorem 7.1.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L720-L848

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepTwo

theorem maximal_badNormalizer_quotient_hasNormalPComplement.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} [U.Normal]
    (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U)
    (hU_card_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ U) := by sorry

end MinimalCounterexampleStepTwo

end OddOrder.Isaacs.Ch07
