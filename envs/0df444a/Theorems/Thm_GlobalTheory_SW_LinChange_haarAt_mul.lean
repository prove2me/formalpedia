-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_haarAt_mul
-- name    : GlobalTheory.SW.LinChange.haarAt_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:33.256843+00:00
-- url     : https://prove2.me/theorems/96d90eb3-1ac0-4298-8c96-f16fa286f459
-- title:
--   Lin Change: haar At mul
-- statement:
--   The Lin Change construction uses the haar At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L200-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L200-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.LinChange.haarAt_mul (R M : ℕ) (hR : 0 < R) (hM : 0 < M) (φ : Matrix κ ι K → ℂ)
    (h : HasLevel R φ) : haarAt (R * M) φ = haarAt R φ := by sorry
