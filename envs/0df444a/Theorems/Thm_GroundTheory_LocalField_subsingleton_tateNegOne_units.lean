-- Prove2me | Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_units
-- name    : GroundTheory.LocalField.subsingleton_tateNegOne_units
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:54.845863+00:00
-- url     : https://prove2.me/theorems/a800cb86-1eed-46bb-99b4-1035cd366f72
-- title:
--   Local Field: subsingleton tate Neg One units
-- statement:
--   The Local Field construction uses the subsingleton tate Neg One units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L81-L87

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.subsingleton_tateNegOne_units [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) Lˣ) := by sorry
