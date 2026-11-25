-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_eq_multiples_index
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.eq_multiples_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:09.696287+00:00
-- url     : https://prove2.me/theorems/423e309f-f48b-479f-9a3a-6a045c00adea
-- title:
--   Profinite Integer: eq multiples index
-- statement:
--   The Profinite Integer construction uses the eq multiples index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L92-L102

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

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.eq_multiples_index {H : AddSubgroup ℤ̂} (hH : H.index ≠ 0) : H = multiples H.index := by sorry
