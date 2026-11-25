-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_index_multiples
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.index_multiples
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:09.038343+00:00
-- url     : https://prove2.me/theorems/4b1f9b6b-8ef8-4065-8f74-0553258520cb
-- title:
--   Profinite Integer: index multiples
-- statement:
--   The Profinite Integer construction uses the index multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L88-L90

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
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

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.index_multiples (n : ℕ+) : (multiples n).index = n := by sorry
