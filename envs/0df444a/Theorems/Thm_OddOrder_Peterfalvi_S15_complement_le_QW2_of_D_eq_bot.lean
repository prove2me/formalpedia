-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_complement_le_QW2_of_D_eq_bot
-- name    : OddOrder.Peterfalvi.S15.complement_le_QW2_of_D_eq_bot
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:14.987569+00:00
-- url     : https://prove2.me/theorems/8c48fc8b-b55a-4a4d-9e3a-f997ed075199
-- title:
--   Peterfalvi (13.17.c) with $D=1$: a Frobenius complement containing $W_1$ lies in $QW_2$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II and $D=1$. Let $L\le G$ be a subgroup, `frob : TypeIFrobeniusData L` is a Frobenius structure on a subgroup $L\le G$ of type I, and $E$ denotes the image in $G$ of its Frobenius complement `frob.complement`. Assume $W_1\le E$. Then
--
--   $$E\le Q\sqcup W_2 .$$
--
--   This is the Huppert step of (13.17.c): $E$ has odd order, so $W_1$ is normal in $E$ and $E\le N_G(W_1)=QW_2$ by (13.16).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Gate3.lean#L819-L891

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem complement_le_QW2_of_D_eq_bot [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥)
    {L : Subgroup G} (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ≤ hyp.Q ⊔ hyp.W2 := by sorry

end OddOrder.Peterfalvi.S15
