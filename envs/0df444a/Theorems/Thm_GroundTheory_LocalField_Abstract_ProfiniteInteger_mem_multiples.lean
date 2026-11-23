-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.mem_multiples
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:26.238855+00:00
-- url     : https://prove2.me/theorems/aa6e5ba4-2f10-405f-849f-0a032dce69a3
-- title:
--   Profinite Integer: mem multiples
-- statement:
--   The Profinite Integer construction uses the mem multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L11-L13

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

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.mem_multiples {n : ℕ} {x : ℤ̂} : x ∈ multiples n ↔ ∃ y : ℤ̂, x = n • y := by sorry
