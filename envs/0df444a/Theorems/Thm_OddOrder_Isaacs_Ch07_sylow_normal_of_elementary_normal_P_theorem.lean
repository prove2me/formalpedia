-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_sylow_normal_of_elementary_normal_P_theorem
-- name    : OddOrder.Isaacs.Ch07.sylow_normal_of_elementary_normal_P_theorem
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:48:17.508607+00:00
-- url     : https://prove2.me/theorems/1cdb58a2-2cee-4484-a1ab-41432ab1ce27
-- title:
--   Isaacs Theorem 7.5 (normal-$P$ theorem): Sylow $p$-subgroups of a $p$-solvable group are normal
-- statement:
--   Let $G$ and $V$ be finite groups and $p\ne2$ a prime. Suppose:
--
--   * $G$ is $p$-separable for the prime set $\{p\}$ (that is, $p$-solvable);
--   * every $2$-subgroup of $G$ is abelian;
--   * $\varphi:G\to\mathrm{Aut}(V)$ is an injective homomorphism (a faithful action of $G$ on $V$);
--   * $V$ is a $p$-group;
--   * for every Sylow $p$-subgroup $P$ of $G$, the index of the fixed-point subgroup $C_V(P)$ in $V$ satisfies $[V:C_V(P)]\le p$.
--
--   Then every Sylow $p$-subgroup $P$ of $G$ is normal:
--   $$P\trianglelefteq G.$$
--
--   The proof is by strong induction on $|G|$. If there are two distinct Sylow subgroups $P,Q$ with $\langle P,Q\rangle\ne G$, one descends to $\langle P,Q\rangle$. When $\langle P,Q\rangle=G$, the index bound forces $|V/U|\le p^2$ for $U=C_V(P)\cap C_V(Q)$, and splitting on whether $V/U$ is cyclic gives a contradiction through the elementary abelian or the cyclic branch.
--
--   **Formalization Note** The $p$-solvability hypothesis is the typeclass `Ch03.IsPiSeparable ({p} : Set ℕ) G`, meaning the $\{p\}$-Fitting series reaches $G$; the fixed-point subgroup is `actionCentralizer φ P`, defined as the fixed points of $P$ acting on $V$ via $\varphi$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean#L1205-L1364

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem sylow_normal_of_elementary_normal_P_theorem
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} (hφ : Function.Injective φ)
    (hV : IsPGroup p V)
    (h_centralizer_index :
      ∀ (P : Sylow p G), (actionCentralizer φ (P : Subgroup G)).index ≤ p)
    (P : Sylow p G) : (P : Subgroup G).Normal := by sorry

end OddOrder.Isaacs.Ch07
