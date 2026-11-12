-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_step8a_PBar_normal_GBar
-- name    : OddOrder.Isaacs.Ch07.step8a_PBar_normal_GBar
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:52:21.11019+00:00
-- url     : https://prove2.me/theorems/216debd8-da8b-491f-99f7-618eb0a88bf8
-- title:
--   Isaacs 7.6, Step 8a: $\bar P\trianglelefteq G/O_p(G)$ under the Step 4--7 outputs
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$. Put $U=O_p(G)$, $V=\Omega_1(Z(U))$ (`omega1ZCenterOpCore G p`), and $\bar G=G/O_p(G)$.
--
--   Let $P$ be a Sylow $p$-subgroup of $G$ with $p\neq 2$. Assume: $G$ is $p$-separable; every $2$-subgroup of $G$ is abelian; $O_{p'}(G)=1$; $C_G(Z(P))=P$. Let $A\in E(P)$ with $UA=P$, $|A:A\cap U|=p$ and $|V:V\cap A|\le p$, and assume that the image of $C_G(V)$ in $\bar G$ is trivial (i.e. $C_G(V)\le O_p(G)$). Then the image $\bar P$ of $P$ in $\bar G$ is a normal subgroup of $\bar G$:
--   $$\bar P\ \trianglelefteq\ G/O_p(G).$$
--
--   This is Step 8a of Isaacs's Theorem 7.6: it applies Theorem 7.5 to the faithful action of $\bar G$ on $V$ to obtain normality of $\bar P$.
--
--   **Formalization Note.** $O_p(G)$ appears both as `opCore p G` and as `oPiCore {p} G` (the $\pi$-core for $\pi=\{p\}$); `Subgroup.relIndex H K` is the index $|K : H\cap K|$. "$p$-separable" is the instance `IsPiSeparable {p} G`. $E(P)$ is `maxElemAbelianIn P p`, the elementary abelian $p$-subgroups of $P$ of maximal order, and $J(P)$ is `Subgroup.thompsonJ P p`, the subgroup they generate.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean#L1136-L1261

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem step8a_PBar_normal_GBar
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (_h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (_h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (_h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G))
    (_h_Abar_card_eq_p :
       (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p)
    (h_V_inter_A_le_p : A.relIndex (omega1ZCenterOpCore G p) ≤ p)
    (h_K_map_eq_bot :
       (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
         (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥) :
    ((P : Subgroup G).map
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).Normal := by sorry

end OddOrder.Isaacs.Ch07
