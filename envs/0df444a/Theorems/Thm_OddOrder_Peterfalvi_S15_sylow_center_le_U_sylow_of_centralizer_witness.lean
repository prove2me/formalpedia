-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_sylow_center_le_U_sylow_of_centralizer_witness
-- name    : OddOrder.Peterfalvi.S15.sylow_center_le_U_sylow_of_centralizer_witness
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:08.451886+00:00
-- url     : https://prove2.me/theorems/24e10c27-6afc-4aac-872b-48604b8d1947
-- title:
--   Peterfalvi (14.6): center trapping, $Z(R)\le R_0$ for $R_0\in\mathrm{Syl}_r(U)$ noncyclic
-- statement:
--   Let $G$ be a finite minimal simple group of odd order and `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package, with subgroups $P,U\le G$. Let $r$ be a prime, let $R_0$ be a noncyclic Sylow $r$-subgroup of $U$, let $K\le G$ with $U\le K$, and let $R$ be a Sylow $r$-subgroup of $K$ whose image contains the image of $R_0$ (under `Subgroup.inclusion`). Let $x\in G$ lie in the image of $R_0$ with $x\ne1$ and $P\cap C_G(x)\ne1$. Then the center of (the image in $G$ of) $R$ is contained in (the image in $G$ of) $R_0$:
--   $$Z(R)\ \le\ R_0 .$$
--
--   The nontrivial point of $P\cap C_G(x)$ places $x$ in the type-$P_2$ support; the TI property gives $C_G(x)\le S$, and the Hall property of $U$ in $S$ forces $Z(R)\le R_0$. It is used in Peterfalvi (14.6).
--
--   **Formalization Note.** Subgroups are transported to $G$ by `Subgroup.map _.subtype`; "$P\cap C_G(x)\ne1$" is `hyp.P ⊓ Subgroup.centralizer {x} ≠ ⊥`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseASylowCenter.lean#L69-L170

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem sylow_center_le_U_sylow_of_centralizer_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) (R : Sylow r ↥K)
    (hR₀R : (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R)
    {x : G} (hxR₀ : x ∈ (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype)
    (hx1 : x ≠ (1 : G))
    (hxP : hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥) :
    (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
        ((R : Subgroup ↥K).map K.subtype).subtype ≤
      (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype := by sorry

end OddOrder.Peterfalvi.S15
