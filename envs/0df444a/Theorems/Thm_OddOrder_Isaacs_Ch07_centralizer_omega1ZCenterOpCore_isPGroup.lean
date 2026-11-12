-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_centralizer_omega1ZCenterOpCore_isPGroup
-- name    : OddOrder.Isaacs.Ch07.centralizer_omega1ZCenterOpCore_isPGroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:50:00.803028+00:00
-- url     : https://prove2.me/theorems/d4cbf1ef-dd5f-47e7-8746-41adc8af871f
-- title:
--   Isaacs 7.6, Step 6: $C_G(\Omega_1(Z(O_p(G))))$ is a $p$-group
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$. Put $V=\Omega_1(Z(O_p(G)))$ (`omega1ZCenterOpCore G p`), the elements of $Z(O_p(G))$ whose $p$-th power is trivial.
--
--   Assume that $G$ is $p$-separable, that $O_{p'}(G)=1$, and that $P$ is a Sylow $p$-subgroup of $G$ with $C_G(Z(P))=P$. Then
--   $$C_G(V)\ \text{is a } p\text{-group.}$$
--
--   This is Step 6 of the proof of Isaacs's Theorem 7.6 (normality of the Thompson subgroup under hypotheses on $p$-separable groups); it is used to show that $G/O_p(G)$ acts faithfully on $V$.
--
--   **Formalization Note.** `IsPGroup p` is the statement that every element has $p$-power order.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean#L189-L271

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem centralizer_omega1ZCenterOpCore_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) := by sorry

end OddOrder.Isaacs.Ch07
