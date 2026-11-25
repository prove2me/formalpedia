-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_injective
-- name    : GroundTheory.ProfCoh.finite_torsN_of_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:42.204353+00:00
-- url     : https://prove2.me/theorems/488da522-ff59-4584-9b9c-f59bd85f1e9d
-- title:
--   Prof Coh: finite tors N of injective
-- statement:
--   The Prof Coh construction uses the finite tors N of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L360-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L360-L362

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

theorem GroundTheory.ProfCoh.finite_torsN_of_injective (hf : Function.Injective f) [Finite (TorsN B n)] :
    Finite (TorsN A n) := by sorry
