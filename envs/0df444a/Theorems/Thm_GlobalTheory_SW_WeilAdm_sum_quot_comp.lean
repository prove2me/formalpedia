-- Prove2me | Theorems.Thm_GlobalTheory_SW_WeilAdm_sum_quot_comp
-- name    : GlobalTheory.SW.WeilAdm.sum_quot_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:23.365587+00:00
-- url     : https://prove2.me/theorems/aa3229fd-47cc-4f88-8dfa-71ecce9f78f2
-- title:
--   Weil Adm: sum quot comp
-- statement:
--   The Weil Adm construction uses the sum quot comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleLatticeFamilyHermitianWeilAction.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleLatticeFamilyHermitianWeilAction.lean#L19-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section

theorem GlobalTheory.SW.WeilAdm.sum_quot_comp {A V : Type} [AddCommGroup A] [AddCommMonoid V] (B : AddSubgroup A)
    [Fintype (A ⧸ B)] (f : A → V) (hf : ∀ x y, x - y ∈ B → f x = f y) (α : A → A)
    (hα : ∀ x y, α x - α y ∈ B → x - y ∈ B) :
    ∑ q : A ⧸ B, f (α q.out) = ∑ q : A ⧸ B, f q.out := by sorry
