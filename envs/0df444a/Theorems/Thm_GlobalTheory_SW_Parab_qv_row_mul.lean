-- Prove2me | Theorems.Thm_GlobalTheory_SW_Parab_qv_row_mul
-- name    : GlobalTheory.SW.Parab.qv_row_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:16.948338+00:00
-- url     : https://prove2.me/theorems/ab820e93-79bc-461f-b9f6-099b6fe27148
-- title:
--   Parab: qv row mul
-- statement:
--   The Parab construction uses the qv row mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L132-L135

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

theorem GlobalTheory.SW.Parab.qv_row_mul {κ ι : Type} [Fintype ι] (x : Matrix κ ι ℚ) (A : Matrix ι ι ℚ) (k : κ) :
    _root_.GlobalTheory.SW.qv ((x * A) k) = _root_.GlobalTheory.SW.qv (x k) ᵥ* _root_.GlobalTheory.SW.qm A := by sorry
