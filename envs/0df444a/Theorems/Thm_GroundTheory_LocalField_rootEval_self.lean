-- Prove2me | Theorems.Thm_GroundTheory_LocalField_rootEval_self
-- name    : GroundTheory.LocalField.rootEval_self
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:27.801886+00:00
-- url     : https://prove2.me/theorems/9e2756b5-2086-5adc-b7af-3f924c8afa35
-- title:
--   Local Field: root Eval self
-- statement:
--   The Local Field construction uses the root Eval self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L72-L73

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)

theorem GroundTheory.LocalField.rootEval_self : rootEval hP (P : B⟦X⟧) = 0 := by sorry
