-- Prove2me | Theorems.Thm_GlobalTheory_CMType_mem_conjugate
-- name    : GlobalTheory.CMType.mem_conjugate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:45.205235+00:00
-- url     : https://prove2.me/theorems/10300ebc-9ce7-5b03-b393-bd918f8ea848
-- title:
--   CMType: mem conjugate
-- statement:
--   The CMType construction uses the mem conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L44-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E]

theorem GlobalTheory.CMType.mem_conjugate (Φ : CMType E) (τ : E →+* ℂ) :
    τ ∈ Φ.conjugate ↔ ComplexEmbedding.conjugate τ ∈ Φ := by sorry
