-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZDual_map_comp
-- name    : GroundTheory.ProfCoh.QZDual.map_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:24.666591+00:00
-- url     : https://prove2.me/theorems/c37d5ab4-6653-5de9-b73d-372d7ddac2ae
-- title:
--   QZDual: map comp
-- statement:
--   The QZDual construction uses the map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L57-L59

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
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
open Topology
open GroundTheory.ProfCoh.QZDual
variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]

theorem GroundTheory.ProfCoh.QZDual.map_comp (g : B →ₜ+ C) (f : A →ₜ+ B) :
    map (g.comp f) = (map f).comp (map g) := by sorry
