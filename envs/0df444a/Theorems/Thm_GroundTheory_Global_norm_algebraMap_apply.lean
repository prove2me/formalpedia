-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_algebraMap_apply
-- name    : GroundTheory.Global.norm_algebraMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:33.950159+00:00
-- url     : https://prove2.me/theorems/dd31aaee-aa03-4d62-9236-8279f1f6d7cb
-- title:
--   Global: norm algebra Map apply
-- statement:
--   The Global construction uses the norm algebra Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L57-L60

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
variable [NumberField K]
omit [NumberField K]

theorem GroundTheory.Global.norm_algebraMap_apply (k : K) (w : InfinitePlace K) :
    ‖algebraMap K K∞ k w‖ = w k := by sorry
