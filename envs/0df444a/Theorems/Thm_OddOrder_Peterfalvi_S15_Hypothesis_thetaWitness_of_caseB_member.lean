-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_thetaWitness_of_caseB_member
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.thetaWitness_of_caseB_member
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:24.015034+00:00
-- url     : https://prove2.me/theorems/acc3c6af-b091-4230-a6a1-266c182a48f9
-- title:
--   Peterfalvi (13.3.b) for $T$: a Clifford case (b) member of $\mathcal S_T$ yields a `ThetaWitness`
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume $vd\ne1$, let `chief : ChiefFactorData` be a chief-factor datum for the type-I/II/III/V setup of $T$, and let `caseB : CliffordCaseBData` be the Clifford case (b) datum for the Section 11 character data of $T$ (`hyp.mkSection11CharacterDataT`). Let $\chi$ be a class function on $T$ which is an irreducible character and lies in the family $\mathcal S_T(H_0\sqcup C')$ of that character data. Then a `ThetaWitness hyp` exists.
--
--   This is the Singer/Galois branch of the $T$-side form of (13.3.b), mirroring the corresponding $S$-side statement for `LambdaWitness`.
--
--   **Formalization Note**. `ThetaWitness` is a project-specific structure; see its definition in the formalization for exactly what it records.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean#L520-L615

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

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in

theorem Hypothesis.thetaWitness_of_caseB_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataT hG hvd chief))
    {χ : ClassFunction ↥hyp.T ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ThetaWitness hyp := by sorry

end OddOrder.Peterfalvi.S15
