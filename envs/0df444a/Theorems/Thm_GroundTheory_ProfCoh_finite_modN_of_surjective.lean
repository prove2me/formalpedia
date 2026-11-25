-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_surjective
-- name    : GroundTheory.ProfCoh.finite_modN_of_surjective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:12.838789+00:00
-- url     : https://prove2.me/theorems/2cc75371-d73b-5925-b5bf-55a703dcbd9f
-- title:
--   Prof Coh: finite mod N of surjective
-- statement:
--   The Prof Coh construction uses the finite mod N of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L364-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L364-L366

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
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {n : ℕ}
  {f : A →+ B} {h : B →+ C}

theorem GroundTheory.ProfCoh.finite_modN_of_surjective (hh : Function.Surjective h) [Finite (ModN B n)] :
    Finite (ModN C n) := by sorry
