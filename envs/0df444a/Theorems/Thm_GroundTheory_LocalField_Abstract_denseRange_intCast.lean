-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_denseRange_intCast
-- name    : GroundTheory.LocalField.Abstract.denseRange_intCast
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:37.842964+00:00
-- url     : https://prove2.me/theorems/001e0c23-2726-4604-a923-e5be7388149e
-- title:
--   Abstract: dense Range int Cast
-- statement:
--   The Abstract construction uses the dense Range int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L24-L43

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger

theorem GroundTheory.LocalField.Abstract.denseRange_intCast : DenseRange (Int.cast : ℤ → ℤ̂) := by sorry
