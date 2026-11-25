-- Prove2me | Theorems.Thm_GroundTheory_Global_isCompact_closure_fundamentalSetInfinite
-- name    : GroundTheory.Global.isCompact_closure_fundamentalSetInfinite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:34.174752+00:00
-- url     : https://prove2.me/theorems/24a416e1-e266-4111-ab64-a8c190ea35d0
-- title:
--   Global: is Compact closure fundamental Set Infinite
-- statement:
--   The Global construction uses the is Compact closure fundamental Set Infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L70-L73

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
open scoped Classical

theorem GroundTheory.Global.isCompact_closure_fundamentalSetInfinite :
    IsCompact (closure (fundamentalSetInfinite K)) := by sorry
