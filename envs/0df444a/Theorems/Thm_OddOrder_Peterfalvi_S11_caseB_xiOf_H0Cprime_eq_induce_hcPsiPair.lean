-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S11_caseB_xiOf_H0Cprime_eq_induce_hcPsiPair
-- name    : OddOrder.Peterfalvi.S11.caseB_xiOf_H0Cprime_eq_induce_hcPsiPair
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T12:06:48.748346+00:00
-- url     : https://prove2.me/theorems/2b4435f5-edf5-4ad5-99ee-8307fb690ce6
-- title:
--   Peterfalvi Section 11, case B: members of $\mathcal X(H_0C')$ are induced from $\mathrm{hcPsiPair}$ characters
-- statement:
--   Let $G$ be a finite group and $M\le G$ a subgroup, with the Peterfalvi Types I--V setup `data : TypesIIIIIIVSetup M` (with subgroup $H$ and parameter $q=$ `data.q`), a chief-factor datum `chief : ChiefFactorData data` (with $p=$ `chief.p` prime, $N$, $H_0$), and the Section 11 character data `chars`. Suppose the data are in Clifford case B (`caseB`), with the instances on the group $HU$ and the subgroup $HC$ as in the statement (finite, normality, `Invertible (Nat.card ·: ℂ)`). Let $\zeta$ be an irreducible character of $HU$ (`huSub data`) lying in the set $\mathcal X(H_0C')$ (`xiOf data (chief.H0 ⊔ cprimeSub data chief)`). Then there exist a nontrivial homomorphism $\bar\theta:H/N\to\mathbb C^\times$ and a homomorphism $\lambda:C\to\mathbb C^\times$ (on `cInHu data chief`) that is trivial on $C'$, such that
--   $$\zeta=\mathrm{Ind}_{HC}^{HU}\ \texttt{hcPsiPair}(\bar\theta,\lambda).$$
--
--   This is the case-B pair exhaustion for $\mathcal X(H_0C')$ in Peterfalvi Section 11, the $C'$-kernel analogue of the $H_0C$ statement.
--
--   **Formalization Note.** `hcPsiPair chief θbar lam` is the linear character of $HC$ built from $\bar\theta$ and $\lambda$; `ClassFunction.induce` is induction from the displayed subgroup of `huSub data`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHomBasic.lean#L164-L386

import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CaseBXi
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHomBasic

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below

theorem caseB_xiOf_H0Cprime_eq_induce_hcPsiPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {ζ : IrreducibleCharacter ↥(huSub data)}
    (hζ : ζ ∈ xiOf data (chief.H0 ⊔ cprimeSub data chief)) :
    ∃ (θbar : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ), θbar ≠ 1 ∧
      (∀ c : ↥(cInHu data chief),
        (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
        lam c = 1) ∧
      (ζ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsiPair chief θbar lam).toClassFunction := by sorry

end OddOrder.Peterfalvi.S11
