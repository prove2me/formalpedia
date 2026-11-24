-- Prove2me | Theorems.Thm_GlobalTheory_SW_Parab_qv_bilin
-- name    : GlobalTheory.SW.Parab.qv_bilin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:23.284381+00:00
-- url     : https://prove2.me/theorems/8e8b95c3-c2c2-4adb-9212-98f9eb81745a
-- title:
--   Parab: qv bilin
-- statement:
--   The Parab construction uses the qv bilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L139-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
open Matrix Complex
open scoped ComplexConjugate Real

theorem GlobalTheory.SW.Parab.qv_bilin {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) (v : ι → ℚ) :
    ((v ⬝ᵥ S *ᵥ v : ℚ) : ℂ) = _root_.GlobalTheory.SW.qv v ⬝ᵥ _root_.GlobalTheory.SW.qm S *ᵥ _root_.GlobalTheory.SW.qv v := by sorry
