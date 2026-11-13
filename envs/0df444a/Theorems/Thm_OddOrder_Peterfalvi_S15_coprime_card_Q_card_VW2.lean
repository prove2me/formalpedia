-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_Q_card_VW2
-- name    : OddOrder.Peterfalvi.S15.coprime_card_Q_card_VW2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:01.42864+00:00
-- url     : https://prove2.me/theorems/af577ca7-d3f1-4052-8de9-0451d1f7c5e1
-- title:
--   Peterfalvi (13.16): $|Q|$ is coprime to $|V\sqcup W_2|$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Then
--
--   $$\gcd\big(|Q|,\ |V\sqcup W_2|\big)=1 .$$
--
--   Here $Q=T_F$ is a normal Hall subgroup of $T$ with complement $V\rtimes W_2$. This is the $W_1$-side coprime-action datum for (13.16).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L589-L684

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem coprime_card_Q_card_VW2 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥(hyp.V ⊔ hyp.W2)) := by sorry

end OddOrder.Peterfalvi.S15
