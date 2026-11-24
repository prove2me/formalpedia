-- Prove2me | Theorems.Thm_GlobalTheory_SW_WeilLevel_hasLevel_of_levelL
-- name    : GlobalTheory.SW.WeilLevel.hasLevel_of_levelL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:35.512478+00:00
-- url     : https://prove2.me/theorems/f4414802-83dd-42c1-8d83-492f62ad9f2f
-- title:
--   Weil Level: has Level of level L
-- statement:
--   The Weil Level construction uses the has Level of level L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLattice.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLattice.lean#L145-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ : Lt E n}
omit [IsCMField E]

theorem GlobalTheory.SW.WeilLevel.hasLevel_of_levelL {s R : ℕ} (h1 : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n)
    (h2 : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ}
    (h : LevelL Λ R φ) : HasLevel (s * R) φ := by sorry
