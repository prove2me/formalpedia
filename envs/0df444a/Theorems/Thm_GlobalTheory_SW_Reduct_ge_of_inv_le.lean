-- Prove2me | Theorems.Thm_GlobalTheory_SW_Reduct_ge_of_inv_le
-- name    : GlobalTheory.SW.Reduct.ge_of_inv_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:04.771524+00:00
-- url     : https://prove2.me/theorems/8dc48808-6248-441c-919a-178eb55f5268
-- title:
--   Reduct: ge of inv le
-- statement:
--   The Reduct construction uses the ge of inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryMoveHermitianHalfSpaceHigh.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryMoveHermitianHalfSpaceHigh.lean#L41-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {N : ℕ}

theorem GlobalTheory.SW.Reduct.ge_of_inv_le {Y M : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosSemidef) (hM : Mᴴ = M)
    (h : Y * M = 1) {T : ℝ} (hT : 0 < T)
    (hle : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef) :
    (Y - ((T⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by sorry
