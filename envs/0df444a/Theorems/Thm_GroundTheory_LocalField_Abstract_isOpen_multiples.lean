-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_isOpen_multiples
-- name    : GroundTheory.LocalField.Abstract.isOpen_multiples
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:10:57.394793+00:00
-- url     : https://prove2.me/theorems/30915335-d9ce-4ce9-9e67-d97d14fb840a
-- title:
--   Abstract: is Open multiples
-- statement:
--   The Abstract construction uses the is Open multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L21-L22

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

theorem GroundTheory.LocalField.Abstract.isOpen_multiples (N : ℕ+) : IsOpen (multiples N : Set ℤ̂) := by sorry
