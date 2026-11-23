-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exact_torsNMap_torsNMap
-- name    : GroundTheory.ProfCoh.exact_torsNMap_torsNMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:43.129828+00:00
-- url     : https://prove2.me/theorems/438a4cb4-b223-47bc-9069-13f2ed8dc219
-- title:
--   Prof Coh: exact tors NMap tors NMap
-- statement:
--   The Prof Coh construction uses the exact tors NMap tors NMap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L240-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L240-L249

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
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
universe u v
open Representation
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)
variable {n} (f : A →+ B) (h : B →+ C) (hh : Function.Surjective h)
variable {f h}
variable (hfh : Function.Exact f h)
include hh hfh
variable (hf : Function.Injective f)
include hf
omit hh

theorem GroundTheory.ProfCoh.exact_torsNMap_torsNMap : Function.Exact (torsNMap n f) (torsNMap n h) := by sorry
