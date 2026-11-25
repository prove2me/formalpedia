-- Prove2me | Theorems.Thm_GlobalTheory_CMType_card_eq_finrank
-- name    : GlobalTheory.CMType.card_eq_finrank
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:40.128485+00:00
-- url     : https://prove2.me/theorems/f00c23cf-9947-53bb-8613-a35ed086a73b
-- title:
--   CMType: card eq finrank
-- statement:
--   The CMType construction uses the card eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L96-L100

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
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)

theorem GlobalTheory.CMType.card_eq_finrank [IsCMField E] :
    Fintype.card Φ = Module.finrank ℚ (maximalRealSubfield E) := by sorry
