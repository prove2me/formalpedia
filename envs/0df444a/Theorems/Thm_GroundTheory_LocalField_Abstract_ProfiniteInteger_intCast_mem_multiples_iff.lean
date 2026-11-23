-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_intCast_mem_multiples_iff
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.intCast_mem_multiples_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:08.616146+00:00
-- url     : https://prove2.me/theorems/6058c625-a0e9-43b1-9463-5957b737c6c9
-- title:
--   Profinite Integer: int Cast mem multiples iff
-- statement:
--   The Profinite Integer construction uses the int Cast mem multiples iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L104-L109

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

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.intCast_mem_multiples_iff {n : ℕ} (hn : 0 < n) {k : ℤ} :
    (k : ℤ̂) ∈ multiples n ↔ (n : ℤ) ∣ k := by sorry
