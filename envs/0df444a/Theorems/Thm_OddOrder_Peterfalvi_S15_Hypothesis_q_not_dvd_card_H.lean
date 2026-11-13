-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_q_not_dvd_card_H
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.q_not_dvd_card_H
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:52:53.9595+00:00
-- url     : https://prove2.me/theorems/bdd212fb-7a1b-41b5-8f9e-cbd4d5960a37
-- title:
--   $q\nmid |H|$ for $H=PC$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Then
--
--   $$q\nmid |H|,\qquad H=PC .$$
--
--   This is the order-theoretic core of the disjointness of $(H^\#)^G$ and $(Q^\#)^G$: $H\le S'=PU$, $q\nmid|P|=p^q$ and $q\nmid|U|$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean#L139-L177

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

theorem Hypothesis.q_not_dvd_card_H [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : ¬ hyp.q ∣ Nat.card ↥hyp.H := by sorry

end CountingLayer

end OddOrder.Peterfalvi.S15
