-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_sylow_isCoatom_of_minimal_counterexample
-- name    : OddOrder.Isaacs.Ch07.sylow_isCoatom_of_minimal_counterexample
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:25.855281+00:00
-- url     : https://prove2.me/theorems/8f357411-5b57-453e-a175-03dd5942e7e1
-- title:
--   Isaacs 7.1, Step 4: a Sylow $p$-subgroup is maximal in a minimal counterexample
-- statement:
--   Say that $G$ satisfies the *Thompson local hypothesis at $p$* (`HasThompsonPComplementHypothesis p G`) if for every Sylow $p$-subgroup $P$ of $G$, both $C_G(Z(P))$ and $N_G(J(P))$ have a normal $p$-complement (`HasNormalPComplement`; a normal subgroup that complements every Sylow $p$-subgroup).
--
--   Let $G$ be a finite group, $p$ a prime, $P$ a Sylow $p$-subgroup of $G$. Assume: $G$ satisfies the Thompson local hypothesis at $p$; every finite group $H$ (same universe) with $|H|<|G|$ satisfying it has a normal $p$-complement; $G$ has no normal $p$-complement; and $G/O_p(G)$ has a normal $p$-complement. Then
--   $$P\ \text{is a maximal proper subgroup of } G .$$
--
--   This is Step 4 in the minimal-counterexample proof of Isaacs's Theorem 7.1.
--
--   **Formalization Note.** Maximality is `IsCoatom (P : Subgroup G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_SylowMaximal.lean#L35-L116

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section MinimalCounterexampleStepFour

theorem sylow_isCoatom_of_minimal_counterexample.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    IsCoatom (P : Subgroup G) := by sorry

end MinimalCounterexampleStepFour

end OddOrder.Isaacs.Ch07
