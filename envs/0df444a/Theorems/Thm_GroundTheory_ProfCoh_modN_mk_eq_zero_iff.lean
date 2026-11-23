-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_modN_mk_eq_zero_iff
-- name    : GroundTheory.ProfCoh.modN_mk_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:25.56213+00:00
-- url     : https://prove2.me/theorems/7109857b-f61d-407d-bb26-9cf09ba58903
-- title:
--   Prof Coh: mod N mk eq zero iff
-- statement:
--   The Prof Coh construction uses the mod N mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L166-L169

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

theorem GroundTheory.ProfCoh.modN_mk_eq_zero_iff (x : A) :
    (Submodule.Quotient.mk x : ModN A n) = 0 ↔ ∃ y : A, n • y = x := by sorry
