-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_thompsonJ_le_opCore_of_normal_J_hypotheses
-- name    : OddOrder.Isaacs.Ch07.thompsonJ_le_opCore_of_normal_J_hypotheses
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-11-12T05:51:26.508436+00:00
-- url     : https://prove2.me/theorems/92313772-b582-465b-9e97-3809c15a846b
-- title:
--   Isaacs 7.6: $J(P)\le O_p(G)$ for $p$-separable $G$ with $O_{p'}(G)=1$, $C_G(Z(P))=P$
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$.
--
--   Let $p\ne 2$ and let $P$ be a Sylow $p$-subgroup of $G$. Assume that $G$ is $p$-separable, that every $2$-subgroup of $G$ is abelian, that $O_{p'}(G)=1$, and that $C_G(Z(P))=P$. Then
--   $$J(P)\ \le\ O_p(G).$$
--
--   This is the core of Isaacs's Theorem 7.6 (Steps 1--7 plus the Step 8 normality), proved by strong induction on $|G|$; it later yields that $J(P)$ is normal in $G$ in the Thompson normal $p$-complement theorem.
--
--   **Formalization Note.** $O_p(G)$ appears both as `opCore p G` and as `oPiCore {p} G` (the $\pi$-core for $\pi=\{p\}$); `Subgroup.relIndex H K` is the index $|K : H\cap K|$. "$p$-separable" is the instance `IsPiSeparable {p} G`. $E(P)$ is `maxElemAbelianIn P p`, the elementary abelian $p$-subgroups of $P$ of maximal order, and $J(P)$ is `Subgroup.thompsonJ P p`, the subgroup they generate.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean#L1308-L1414

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem thompsonJ_le_opCore_of_normal_J_hypotheses
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G := by sorry

end OddOrder.Isaacs.Ch07
