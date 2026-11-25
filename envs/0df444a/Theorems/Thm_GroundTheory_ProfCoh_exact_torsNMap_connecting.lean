-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exact_torsNMap_connecting
-- name    : GroundTheory.ProfCoh.exact_torsNMap_connecting
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:53.073147+00:00
-- url     : https://prove2.me/theorems/7ba3a559-4cb3-4644-a69d-fbed5e458abe
-- title:
--   Prof Coh: exact tors NMap connecting
-- statement:
--   The Prof Coh construction uses the exact tors NMap connecting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L251-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L251-L264

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

theorem GroundTheory.ProfCoh.exact_torsNMap_connecting : Function.Exact (torsNMap n h) (connecting hh hfh hf) := by sorry
