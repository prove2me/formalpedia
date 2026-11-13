-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_complement_inf_Q_eq_W1
-- name    : OddOrder.Peterfalvi.S15.complement_inf_Q_eq_W1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:22.840462+00:00
-- url     : https://prove2.me/theorems/8aed7136-d415-4e89-b808-7701152db82e
-- title:
--   Peterfalvi (13.17.c): $E\cap Q=W_1$ for a Frobenius complement $E$ containing $W_1$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $T$ is of type II (`IsTypeII hyp.T`). Let $L\le G$ be a subgroup, `frob : TypeIFrobeniusData L` is a Frobenius structure on a subgroup $L\le G$ of type I, and $E$ denotes the image in $G$ of its Frobenius complement `frob.complement`. Assume $W_1\le E$. Then
--
--   $$E\cap Q=W_1 .$$
--
--   This is the proved half of the intersection structure in (13.17.c) (Pf p. 82).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_ComplementStructure.lean#L24-L78

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem complement_inf_Q_eq_W1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ⊓ hyp.Q = hyp.W1 := by sorry

end OddOrder.Peterfalvi.S15
