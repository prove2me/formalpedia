-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_multiples
-- name    : GroundTheory.LocalField.Abstract.isClosed_multiples
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:53.600118+00:00
-- url     : https://prove2.me/theorems/29784f5e-1542-4bc9-8e31-1080d9712677
-- title:
--   Abstract: is Closed multiples
-- statement:
--   The Abstract construction uses the is Closed multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L11-L16

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

theorem GroundTheory.LocalField.Abstract.isClosed_multiples (N : ℕ) : IsClosed (multiples N : Set ℤ̂) := by sorry
