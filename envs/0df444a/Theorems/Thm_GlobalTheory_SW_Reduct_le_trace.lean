-- Prove2me | Theorems.Thm_GlobalTheory_SW_Reduct_le_trace
-- name    : GlobalTheory.SW.Reduct.le_trace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:44:53.402637+00:00
-- url     : https://prove2.me/theorems/4895edbb-c043-46a7-9a99-901279db2ace
-- title:
--   Reduct: le trace
-- statement:
--   The Reduct construction uses the le trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryMoveHermitianHalfSpaceHigh.lean#L17-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryMoveHermitianHalfSpaceHigh.lean#L17-L39

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

theorem GlobalTheory.SW.Reduct.le_trace {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.PosSemidef) {T : ℝ}
    (hT : M.trace.re ≤ T) : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef := by sorry
