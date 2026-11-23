-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_haarAt_mul
-- name    : GlobalTheory.SW.HaarLevel.haarAt_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:48:51.523532+00:00
-- url     : https://prove2.me/theorems/7dfc2fdb-488b-4287-aaf9-ca9b90d75aaf
-- title:
--   Haar Level: haar At mul
-- statement:
--   The Haar Level construction uses the haar At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L136-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L136-L145

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

theorem GlobalTheory.SW.HaarLevel.haarAt_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) {S : ℕ}
    (hS : 0 < S) : haarAt (R * S) φ = haarAt R φ := by sorry
