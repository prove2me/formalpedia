-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_nsmul_cancel
-- name    : GlobalTheory.SW.HaarLevel.nsmul_cancel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:45.417348+00:00
-- url     : https://prove2.me/theorems/281a00d7-1cee-4737-a738-0f200b55287f
-- title:
--   Haar Level: nsmul cancel
-- statement:
--   The Haar Level construction uses the nsmul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L82-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
omit [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.HaarLevel.nsmul_cancel {R : ℕ} (hR : 0 < R) {x y : Matrix κ ι K} : R • x = R • y ↔ x = y := by sorry
