-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_step3_Abar_centralizes_inter_LBar
-- name    : OddOrder.Isaacs.Ch07.step3_Abar_centralizes_inter_LBar
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:51:39.644847+00:00
-- url     : https://prove2.me/theorems/c5bd49b0-59c2-45ef-9c23-841ea3fbe271
-- title:
--   Isaacs 7.6, Step 3: $[O_{p',p}(G)\cap H,\,A]\le O_p(G)$ for proper $H\supseteq O_p(G)A$
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$. Put $U=O_p(G)$ and $L=O_{p',p}(G)$ (`opPpPrimeCore G p`), the preimage in $G$ of $O_{p'}(G/U)$.
--
--   Assume $p\ne 2$, $G$ is $p$-separable, every $2$-subgroup of $G$ is abelian, $O_{p'}(G)=1$, $P$ is a Sylow $p$-subgroup of $G$ with $C_G(Z(P))=P$, together with the induction hypothesis `ih`: for every finite group $H$ (in the same universe as $G$) with $|H|<|G|$ that is $p$-separable, has all $2$-subgroups abelian and $O_{p'}(H)=1$, and for every Sylow $p$-subgroup $Q$ of $H$ with $C_H(Z(Q))=Q$, the Thompson subgroup $J(Q)$ is normal in $H$. Let $A\in E(P)$, and let $H\ne G$ be a proper subgroup with $UA\le H$. Let $S$ be a Sylow $p$-subgroup of the group $H$ whose underlying subgroup equals $H\cap P$. Then
--   $$[\,L\cap H,\ A\,]\ \le\ U .$$
--   Equivalently, $\bar A$ centralizes the image of $L\cap H$ in $G/U$.
--
--   This is the induction-consuming core (Step 3) of the proof of Isaacs's Theorem 7.6; it yields $P=UA$ in Step 4.
--
--   **Formalization Note.** The hypothesis $p\ne2$ appears as `_hp2` and is not used by the proof, but it is a hypothesis of the statement. The theorem carries an explicit universe `u`.
--
--   **Formalization Note.** $O_p(G)$ appears both as `opCore p G` and as `oPiCore {p} G` (the $\pi$-core for $\pi=\{p\}$); `Subgroup.relIndex H K` is the index $|K : H\cap K|$. "$p$-separable" is the instance `IsPiSeparable {p} G`. $E(P)$ is `maxElemAbelianIn P p`, the elementary abelian $p$-subgroups of $P$ of maximal order, and $J(P)$ is `Subgroup.thompsonJ P p`, the subgroup they generate.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean#L262-L478

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem step3_Abar_centralizes_inter_LBar.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (_hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    {H : Subgroup G}
    (hH_ne_top : H ≠ ⊤)
    (hUA_le_H : OddOrder.Isaacs.Ch01.opCore p G ⊔ A ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    (⁅opPpPrimeCore G p ⊓ H, A⁆ : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G := by sorry

end OddOrder.Isaacs.Ch07
