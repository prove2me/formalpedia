-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZDual_card_eq
-- name    : GroundTheory.ProfCoh.QZDual.card_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:02.176993+00:00
-- url     : https://prove2.me/theorems/7a0e6ae3-03fc-4371-8689-da5577d5d7bc
-- title:
--   QZDual: card eq
-- statement:
--   The QZDual construction uses the card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L161-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L161-L162

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Function
open GroundTheory.ProfCoh.QZDual
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]

theorem GroundTheory.ProfCoh.QZDual.card_eq [Finite N] : Nat.card (QZDual N) = Nat.card N := by sorry
