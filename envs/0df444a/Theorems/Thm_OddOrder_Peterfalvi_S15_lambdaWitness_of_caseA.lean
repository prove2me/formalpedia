-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseA
-- name    : OddOrder.Peterfalvi.S15.lambdaWitness_of_caseA
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:06:07.777857+00:00
-- url     : https://prove2.me/theorems/6fb58608-a721-42a8-bbfd-5f63e038eed4
-- title:
--   Peterfalvi (13.3.b): Clifford case (a) always yields a `LambdaWitness`
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `chief : ChiefFactorData` be a chief-factor datum for the type-I/II/III/V setup of $S$ (`hyp.toTypesIIIIIIVSetupS hG`) and `caseA : CliffordCaseAData` a Clifford case (a) datum for the Section 11 character data of $S$ (`hyp.mkSection11CharacterDataS`). Then a `LambdaWitness hyp` exists.
--
--   This is the unconditional branch of (13.3.b), obtained from the degree-$qu$ irreducible member of Peterfalvi (9.8.c).
--
--   **Formalization Note**. `LambdaWitness` is a project-specific structure; the description follows the source docstring (a degree-$uq$ irreducible induced from a linear character of $PC$).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean#L304-L416

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

theorem lambdaWitness_of_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData (hyp.mkSection11CharacterDataS hG chief)) :
    LambdaWitness hyp := by sorry

end OddOrder.Peterfalvi.S15
