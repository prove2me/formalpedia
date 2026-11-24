-- Prove2me | Theorems.Thm_GlobalTheory_SW_Parab_isSB_parChar_mul
-- name    : GlobalTheory.SW.Parab.isSB_parChar_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:12.541548+00:00
-- url     : https://prove2.me/theorems/32ef5506-b171-4de9-b6c1-09ff8f4edc3e
-- title:
--   Parab: is SB par Char mul
-- statement:
--   The Parab construction uses the is SB par Char mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L66-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L66-L128

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

theorem GlobalTheory.SW.Parab.isSB_parChar_mul {κ ι : Type} [Fintype κ] [Fintype ι] (S : Matrix ι ι ℚ)
    (φ : Matrix κ ι ℚ → ℂ) (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB fun x => _root_.GlobalTheory.SW.Parab.parChar S x * φ x := by sorry
