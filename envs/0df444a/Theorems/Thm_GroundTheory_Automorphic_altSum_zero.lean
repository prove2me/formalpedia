-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_altSum_zero
-- name    : GroundTheory.Automorphic.altSum_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:06.170262+00:00
-- url     : https://prove2.me/theorems/377b76fc-e990-46b6-97d0-723e14198adb
-- title:
--   Automorphic: alt Sum zero
-- statement:
--   The Automorphic construction uses the alt Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/AltSum.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/AltSum.lean#L14-L14

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GroundTheory GroundTheory.Automorphic
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

theorem GroundTheory.Automorphic.altSum_zero (h : V → W) (y : Fin 0 → V) (s : V) : altSum 0 h y s = h s := by sorry

attribute [defeq] GroundTheory.Automorphic.altSum_zero
