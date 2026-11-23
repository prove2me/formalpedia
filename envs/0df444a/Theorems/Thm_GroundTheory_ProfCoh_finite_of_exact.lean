-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_of_exact
-- name    : GroundTheory.ProfCoh.finite_of_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:05.685322+00:00
-- url     : https://prove2.me/theorems/28afa7dc-8267-40bf-97f6-f5cbfbdeab37
-- title:
--   Prof Coh: finite of exact
-- statement:
--   The Prof Coh construction uses the finite of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L29-L33

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

theorem GroundTheory.ProfCoh.finite_of_exact {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (f : X →+ Y) (g : Y →+ Z) (hfg : Function.Exact f g) [Finite X] [Finite Z] : Finite Y := by sorry
