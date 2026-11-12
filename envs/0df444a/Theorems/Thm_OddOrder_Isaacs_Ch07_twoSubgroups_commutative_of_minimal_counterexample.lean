-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_twoSubgroups_commutative_of_minimal_counterexample
-- name    : OddOrder.Isaacs.Ch07.twoSubgroups_commutative_of_minimal_counterexample
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:21.453209+00:00
-- url     : https://prove2.me/theorems/95bdc376-1093-46c2-a7be-c3ed7a427f8a
-- title:
--   Isaacs 7.1, Step 6: $2$-subgroups are abelian in a minimal counterexample, $p\ne2$
-- statement:
--   Say that $G$ satisfies the *Thompson local hypothesis at $p$* (`HasThompsonPComplementHypothesis p G`) if for every Sylow $p$-subgroup $P$ of $G$, both $C_G(Z(P))$ and $N_G(J(P))$ have a normal $p$-complement (`HasNormalPComplement`; a normal subgroup that complements every Sylow $p$-subgroup).
--
--   Let $G$ be a finite group, $p\neq 2$ a prime, $P$ a Sylow $p$-subgroup, and assume: $G$ satisfies the Thompson local hypothesis at $p$; the induction hypothesis that every finite group $H$ (in the same universe) with $|H|<|G|$ satisfying the Thompson local hypothesis at $p$ has a normal $p$-complement; $G$ has no normal $p$-complement; and $G/O_p(G)$ has a normal $p$-complement. Then
--   $$\forall S\le G,\ \ S\ \text{a }2\text{-group}\ \Longrightarrow\ S\ \text{is abelian.}$$
--
--   This is Step 6 of the proof of Isaacs's Theorem 7.1, supplying the abelian-$2$-subgroup hypothesis of Theorem 7.6.
--
--   **Formalization Note.** The Sylow subgroup $P$ is an argument of the theorem but does not occur in the conclusion; "$2$-group" is `IsPGroup 2 S`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_AbelianQuotientComplement.lean#L225-L318

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped IsMulCommutative

section MinimalCounterexampleStepSix

theorem twoSubgroups_commutative_of_minimal_counterexample.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp2 : p ≠ 2)
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    ∀ S : Subgroup G, IsPGroup 2 S →
      ∀ x y : ↥S, x * y = y * x := by sorry

end MinimalCounterexampleStepSix

end OddOrder.Isaacs.Ch07
