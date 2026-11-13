-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_exists_conj_typeP_U_of_coprime
-- name    : OddOrder.Peterfalvi.S15.exists_conj_typeP_U_of_coprime
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:27.227205+00:00
-- url     : https://prove2.me/theorems/04f77a29-14b7-45e5-93ae-4f4e19f459c1
-- title:
--   Schur-Zassenhaus for (13.17): $U$ is $S$-conjugate to the type-data complement
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `tdata : TypeIIData hyp.S` be a type II datum for $S$ with type P data `tdata.typeP`, and assume $\gcd(|U|,|P|)=1$. Then there exists $x\in S$ with
--
--   $$U=x\,(\text{`tdata.typeP.U`})\,x^{-1}.$$
--
--   Both $U$ and `tdata.typeP.U` complement the normal Hall subgroup $P$ in $S'$, so this follows from Schur-Zassenhaus conjugacy; it discharges the conjugacy hypothesis in the (13.17) coherence bridge.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTDefs.lean#L882-L978

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

theorem exists_conj_typeP_U_of_coprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (tdata : TypeIIData hyp.S)
    (hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P)) :
    ∃ x : G, x ∈ hyp.S ∧ hyp.U = MulAut.conj x • tdata.typeP.U := by sorry

end OddOrder.Peterfalvi.S15
