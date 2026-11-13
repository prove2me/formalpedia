-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_hypothesis76_zeta_inner_alphaFun_eq_zero
-- name    : OddOrder.Peterfalvi.S15.hypothesis76_zeta_inner_alphaFun_eq_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:47:23.427284+00:00
-- url     : https://prove2.me/theorems/da152bfa-7584-4e8d-aeb3-672916689f26
-- title:
--   Generic (13.5.a): a non-kernel family member is orthogonal to the kernel tail $\alpha$
-- statement:
--   Let $G$ be a finite group (`Fintype G`, $|G|$ invertible in $\mathbb C$), $A\subseteq G$ a subset and $L\le G$ a subgroup, and let `H76 : Hypothesis76 G A L` be the (7.6) hypothesis, with characters $\zeta_0,\dots,\zeta_n$ of $L$. Let $P'\le L$ be a subgroup, $\chi$ a class function on $G$, and $i_1$ an index with $P'\not\subseteq\ker\zeta_{i_1}$. Let $\alpha=$ `hypothesis76AlphaFun H76 P' χ`, a function on $L$. Then
--
--   $$\sum_{x\in L}\zeta_{i_1}(x)\,\overline{\alpha(x)}=0 .$$
--
--   This is the $P'$-kernel orthogonality of the generic (13.5.a): each constituent of the kernel tail comes from a different fibre.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean#L332-L380

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section GenericAlpha

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in

theorem hypothesis76_zeta_inner_alphaFun_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) (i₁ : Fin (H76.n + 1))
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁))) :
    ∑ x : ↥L, H76.zeta i₁ x * (starRingEnd ℂ) (hypothesis76AlphaFun H76 P' χ x) = 0 := by sorry

end GenericAlpha

end OddOrder.Peterfalvi.S15
