-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_U_card_P_of_disjoint
-- name    : OddOrder.Peterfalvi.S15.coprime_card_U_card_P_of_disjoint
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:44.092827+00:00
-- url     : https://prove2.me/theorems/ec6b0e9a-1a9c-4df5-aa7e-66c7955fa4a5
-- title:
--   Coprimality of $|U|$ and $|P|$ from $P\cap U=1$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `tdata : TypeIIData hyp.S` be a type II datum for $S$ and assume $P\cap U=1$. Then
--
--   $$\gcd(|U|,|P|)=1 .$$
--
--   This is the derivable half of the (13.2) faithfulness datum: $P=S_F$ is a relative Hall subgroup of $S'=PU$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTDefs.lean#L1041-L1094

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem coprime_card_U_card_P_of_disjoint [Finite G]
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.S) (hdisj : hyp.P ⊓ hyp.U = ⊥) :
    Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) := by sorry

end OddOrder.Peterfalvi.S15
