-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisTrans_exists_sub_posSemidef
-- name    : GlobalTheory.SW.EisTrans.exists_sub_posSemidef
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:55.466545+00:00
-- url     : https://prove2.me/theorems/bae3fd9f-400b-5af9-a912-3bd9987e6e2c
-- title:
--   Eis Trans: exists sub pos Semidef
-- statement:
--   The Eis Trans construction uses the exists sub pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisAutomorphyLinear.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisAutomorphyLinear.lean#L20-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisTrans
variable {N : ℕ}
open scoped MatrixOrder

theorem GlobalTheory.SW.EisTrans.exists_sub_posSemidef {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ (Y - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by sorry
