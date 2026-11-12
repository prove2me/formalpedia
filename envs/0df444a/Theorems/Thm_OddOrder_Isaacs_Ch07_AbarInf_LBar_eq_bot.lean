-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_AbarInf_LBar_eq_bot
-- name    : OddOrder.Isaacs.Ch07.AbarInf_LBar_eq_bot
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:36.299202+00:00
-- url     : https://prove2.me/theorems/69723c49-4991-4767-b765-f963df8352ce
-- title:
--   Isaacs 7.6, Step 5 prep: $\bar A\cap O_{p'}(G/O_p(G))=1$ for a $p$-subgroup $A$
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$. Let $\bar G=G/O_p(G)$ (the quotient by `oPiCore {p} G`).
--
--   For every $p$-subgroup $A\le G$, the image $\bar A$ of $A$ in $\bar G$ intersects $O_{p'}(\bar G)$ trivially:
--   $$\bar A\cap O_{p'}(\bar G)=1.$$
--
--   It is used in Step 5 of Isaacs's Theorem 7.6, where $\bar A$ is shown to act faithfully and coprimely on $O_{p'}(\bar G)$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean#L194-L237

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem AbarInf_LBar_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA_pg : IsPGroup p A) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) = ⊥ := by sorry

end OddOrder.Isaacs.Ch07
