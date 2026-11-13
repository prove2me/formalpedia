-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_W2_within_S_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.normalizer_W2_within_S_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:07:32.474202+00:00
-- url     : https://prove2.me/theorems/ea02089e-f4bc-41a4-b06b-d41e76f46182
-- title:
--   Peterfalvi (13.16): $N_G(W_2)\cap S\le PW_1$ when $c=1$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $c=1$. Then
--
--   $$N_G(W_2)\cap S\ \le\ P\sqcup W_1 .$$
--
--   This is the $S$-internal part of the (13.16) confinement of $N_G(W_2)$, obtained via the Dedekind modular law from $U\cap N_G(W_2)=1$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTDefs.lean#L682-L774

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

theorem normalizer_W2_within_S_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    Subgroup.normalizer (hyp.W2 : Set G) ⊓ hyp.S ≤ hyp.P ⊔ hyp.W1 := by sorry

end OddOrder.Peterfalvi.S15
