-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.u_le_cyclotomicQuotient
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:38:47.277773+00:00
-- url     : https://prove2.me/theorems/cc892304-2a92-43a8-a7ec-086f9b165d9d
-- title:
--   Peterfalvi (13.2.c)/(9.7): the bound $u\le(p^q-1)/(p-1)$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Then
--
--   $$u\le\frac{p^q-1}{p-1}$$
--
--   (natural-number division). This is the Singer-type bound on $u$ for the type P$_2$ subgroup $S$, obtained from the unconditional Section 9/11 bound.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean#L1166-L1224

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_SubcoherenceInputs
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerLineBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearImprimitiveBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LineScalarCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AInvariantSubrep
import Definitions.Def_OddOrder_Peterfalvi_S11_SingleFactorCentralizer
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenPairAdjoin
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem Hypothesis.u_le_cyclotomicQuotient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := by sorry

end OddOrder.Peterfalvi.S15
