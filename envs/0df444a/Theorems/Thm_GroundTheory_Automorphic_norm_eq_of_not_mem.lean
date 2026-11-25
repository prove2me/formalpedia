-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_norm_eq_of_not_mem
-- name    : GroundTheory.Automorphic.norm_eq_of_not_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:42.81586+00:00
-- url     : https://prove2.me/theorems/a0faefc9-2e5a-4d83-afb6-be71f9c5545e
-- title:
--   Automorphic: norm eq of not mem
-- statement:
--   The Automorphic construction uses the norm eq of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L91-L97

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]
variable {F E}
variable [Algebra.IsQuadraticExtension F E]

theorem GroundTheory.Automorphic.norm_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.norm F x = -(basisOneOf hx).repr (x * x) 0 := by sorry
