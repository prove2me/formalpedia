-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_exact
-- name    : GroundTheory.ProfCoh.finite_modN_of_exact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:42.097448+00:00
-- url     : https://prove2.me/theorems/8bc1a436-6c5c-4fe5-b6d3-7b67a8b7599d
-- title:
--   Prof Coh: finite mod N of exact
-- statement:
--   The Prof Coh construction uses the finite mod N of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L355-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L355-L358

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

theorem GroundTheory.ProfCoh.finite_modN_of_exact (hh : Function.Surjective h) (hfh : Function.Exact f h)
    [Finite (ModN A n)] [Finite (ModN C n)] : Finite (ModN B n) := by sorry
