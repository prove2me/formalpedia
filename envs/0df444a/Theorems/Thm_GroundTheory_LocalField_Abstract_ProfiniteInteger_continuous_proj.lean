-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_continuous_proj
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.continuous_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:52.407012+00:00
-- url     : https://prove2.me/theorems/a720ab52-6ebc-4ee6-b3c9-82f3f883bc45
-- title:
--   Profinite Integer: continuous proj
-- statement:
--   The Profinite Integer construction uses the continuous proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean#L48-L49

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
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
open GroundTheory.LocalField.Abstract.ProfiniteInteger

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.continuous_proj (n : ℕ+) : Continuous (proj n) := by sorry
