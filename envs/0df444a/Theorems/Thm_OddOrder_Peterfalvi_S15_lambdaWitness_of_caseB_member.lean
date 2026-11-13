-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseB_member
-- name    : OddOrder.Peterfalvi.S15.lambdaWitness_of_caseB_member
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:06:59.991741+00:00
-- url     : https://prove2.me/theorems/c7d86061-b513-4775-af45-be0b230145be
-- title:
--   Peterfalvi (13.3.b): a Clifford case (b) member of $\mathcal S(H_0\sqcup C')$ yields a `LambdaWitness`
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `chief : ChiefFactorData` be a chief-factor datum for the type-I/II/III/V setup of $S$ (`hyp.toTypesIIIIIIVSetupS hG`), and let `caseB : CliffordCaseBData` be a Clifford case (b) datum for the Section 11 character data of $S$ (`hyp.mkSection11CharacterDataS`). Let $\chi$ be a class function on $S$ which is an irreducible character and lies in the family $\mathcal S(H_0\sqcup C')$ of that character data. Then a `LambdaWitness hyp` exists.
--
--   Informally the witness is a character of degree $uq$ induced from a linear character of $PC$ which is irreducible. This is the Singer/Galois branch of (13.3.b).
--
--   **Formalization Note**. `LambdaWitness` is a project-specific structure; the description above follows the source docstring.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean#L194-L302

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

theorem lambdaWitness_of_caseB_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData (hyp.mkSection11CharacterDataS hG chief))
    {χ : ClassFunction ↥hyp.S ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    LambdaWitness hyp := by sorry

end OddOrder.Peterfalvi.S15
