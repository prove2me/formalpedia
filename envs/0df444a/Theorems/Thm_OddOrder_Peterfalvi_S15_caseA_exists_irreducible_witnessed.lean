-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_exists_irreducible_witnessed
-- name    : OddOrder.Peterfalvi.S15.caseA_exists_irreducible_witnessed
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:04.147199+00:00
-- url     : https://prove2.me/theorems/6a9c9902-d35a-41b4-965c-92887c1a2e25
-- title:
--   Peterfalvi (9.8.c) with an explicit regular seed: an irreducible degree-$qu$ member of $\mathcal S(H_0C)$
-- statement:
--   Let $G$ be a finite group with `IsMinimalSimpleOdd G`, $M\le G$ a subgroup with `data : TypesIIIIIIVSetup M`, `chief : ChiefFactorData data`, `chars : Section11CharacterData data chief`, and `caseA : CliffordCaseAData chars` a Clifford case (a) datum. Assume the finiteness, invertibility, `Fintype` and normality instances displayed in the statement for the groups `hInHu data`, `huSub data` and `hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)`, and that $\mathrm{Hom}(H/N,\mathbb C^\times)$ is finite ($H=$ `data.H`, $N=$ `chief.N`). Then there is a linear character $\theta:H/N\to\mathbb C^\times$ such that
--
--   - $\theta\ne1$;
--   - for every $i$, the restriction of $\theta$ to the Clifford summand `caseA.Hpart i` is nontrivial;
--   - the character `induceHU data (ClassFunction.induce _ (hcPsi chief θ).toClassFunction)` is irreducible.
--
--   Here `hcPsi chief θ` is the character of $HC$-type groups attached to $\theta$, it is induced to the group `hInHu ⊔ …` and then to $M$ via `induceHU`. This exposes the regular seed $\theta$ behind the parity argument of (9.8.c) so that the shape $\mathrm{Ind}_{HC}(\text{linear})$ can be recovered.
--
--   **Formalization Note**. The exact subgroups involved are encoded through the project's `hInHu`, `huSub`, `cSub`, `hcPsi`, `induceHU` definitions.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean#L128-L192

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

theorem caseA_exists_irreducible_witnessed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [Finite ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Finite ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ, θ ≠ 1 ∧
      (∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1) ∧
      IsIrreducibleCharacter (induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ).toClassFunction)) := by sorry

end OddOrder.Peterfalvi.S15
