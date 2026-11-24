-- Prove2me | Theorems.Thm_GlobalTheory_SW_Parab_parChar_mul_conj
-- name    : GlobalTheory.SW.Parab.parChar_mul_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:49.342279+00:00
-- url     : https://prove2.me/theorems/996437eb-804c-4585-9903-19e0eede8f19
-- title:
--   Parab: par Char mul conj
-- statement:
--   The Parab construction uses the par Char mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L32-L38

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

theorem GlobalTheory.SW.Parab.parChar_mul_conj {κ ι : Type} [Fintype κ] [Fintype ι]
    (S : Matrix ι ι ℚ) (x : Matrix κ ι ℚ) :
    _root_.GlobalTheory.SW.Parab.parChar S x * conj (_root_.GlobalTheory.SW.Parab.parChar S x) = 1 := by sorry
