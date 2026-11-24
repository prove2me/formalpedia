-- Prove2me | Theorems.Thm_GlobalTheory_SW_WeilLevel_levelL_mul
-- name    : GlobalTheory.SW.WeilLevel.levelL_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:08.207206+00:00
-- url     : https://prove2.me/theorems/df940cdd-f388-4b18-b64d-cf1aed333b66
-- title:
--   Weil Level: level L mul
-- statement:
--   The Weil Level construction uses the level L mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLattice.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLattice.lean#L138-L142

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

theorem GlobalTheory.SW.WeilLevel.levelL_mul {R : ℕ} {φ : Matrix (Fin n) (Fin N) E → ℂ} (h : LevelL Λ R φ) (m : ℕ) :
    LevelL Λ (m * R) φ := by sorry
