-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mul_conj
-- name    : GroundTheory.Automorphic.mul_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:55.140841+00:00
-- url     : https://prove2.me/theorems/4a24a09c-e12d-44a1-bcde-b3f67b28b447
-- title:
--   Automorphic: mul conj
-- statement:
--   The Automorphic construction uses the mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L152-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L152-L159

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

theorem GroundTheory.Automorphic.mul_conj (x : E) : x * conj F E x = algebraMap F E (Algebra.norm F x) := by sorry
