-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_quotientComplement_isMulCommutative_of_sylow_isCoatom
-- name    : OddOrder.Isaacs.Ch07.quotientComplement_isMulCommutative_of_sylow_isCoatom
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:57:19.564439+00:00
-- url     : https://prove2.me/theorems/a311acaa-b250-4be3-bf3f-635c7b65ab35
-- title:
--   Isaacs 7.1, Step 6: a normal $p$-complement of $G/O_p(G)$ is abelian when Sylow $P$ is maximal
-- statement:
--   Let $G$ be a finite group, $p$ a prime, and $P$ a Sylow $p$-subgroup of $G$ that is a maximal proper subgroup of $G$ (`IsCoatom`). Let $\bar N$ be a normal subgroup of $G/O_p(G)$ that is a complement (`IsComplement'`) of every Sylow $p$-subgroup of $G/O_p(G)$. Then
--   $$\bar N\ \text{is abelian.}$$
--
--   This is Step 6 in the minimal-counterexample argument for Isaacs's Theorem 7.1 (Thompson's normal $p$-complement theorem); it is used to show that $2$-subgroups are abelian.
--
--   **Formalization Note.** Abelian-ness is `IsMulCommutative ↥Nbar`. The quotient is by `opCore p G`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_AbelianQuotientComplement.lean#L22-L223

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped IsMulCommutative

section MinimalCounterexampleStepSix

theorem quotientComplement_isMulCommutative_of_sylow_isCoatom.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP_max : IsCoatom (P : Subgroup G))
    {Nbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)}
    (hNbar_normal : Nbar.Normal)
    (hNbar_complement : ∀ Pbar : Sylow p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G),
      Subgroup.IsComplement' Nbar (Pbar : Subgroup
        (G ⧸ OddOrder.Isaacs.Ch01.opCore p G))) :
    IsMulCommutative ↥Nbar := by sorry

end MinimalCounterexampleStepSix

end OddOrder.Isaacs.Ch07
