-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_isTrivialOn_stdChar_zero
-- name    : GroundTheory.LocalField.Padic.isTrivialOn_stdChar_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:58.418157+00:00
-- url     : https://prove2.me/theorems/87696b0a-52df-5deb-9074-a641101b5734
-- title:
--   Padic: is Trivial On std Char zero
-- statement:
--   The Padic construction uses the is Trivial On std Char zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L197-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L197-L198

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
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
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]

theorem GroundTheory.LocalField.Padic.isTrivialOn_stdChar_zero : IsTrivialOn (stdChar p) 0 := by sorry
