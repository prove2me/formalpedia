-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_haar_eq_haarAt
-- name    : GlobalTheory.SW.LinChange.haar_eq_haarAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:48.974799+00:00
-- url     : https://prove2.me/theorems/6373e34e-f8cc-4fb9-8a8e-50524b96717d
-- title:
--   Lin Change: haar eq haar At
-- statement:
--   The Lin Change construction uses the haar eq haar At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L204-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L204-L208

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

theorem GlobalTheory.SW.LinChange.haar_eq_haarAt {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) :
    haar φ = haarAt R φ := by sorry
