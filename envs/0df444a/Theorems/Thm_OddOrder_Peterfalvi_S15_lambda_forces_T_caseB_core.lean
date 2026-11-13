-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_forces_T_caseB_core
-- name    : OddOrder.Peterfalvi.S15.lambda_forces_T_caseB_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:06:37.554898+00:00
-- url     : https://prove2.me/theorems/d316172b-16ef-47ce-892d-efb0955c9de1
-- title:
--   Peterfalvi (13.4): the $\lambda$-cluster forces $D=1$, $v=(q^p-1)/(q-1)$ and $|Q|=q^p$ (Core form)
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `core : CharacterDegreeCore hyp`, `lam : LambdaClusterData hyp` (the $\lambda$-cluster) and `pins : NuGridSupplyData hyp`. Then
--
--   $$D=1,\qquad v=\frac{q^p-1}{q-1},\qquad |Q|=q^p$$
--
--   (natural-number division in the middle equation). Informally: if $\mathcal S$ contains the $\lambda$-cluster, case (9.7.b) holds for $T$ with these parameters.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean#L1100-L1176

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in

theorem lambda_forces_T_caseB_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by sorry

end OddOrder.Peterfalvi.S15
