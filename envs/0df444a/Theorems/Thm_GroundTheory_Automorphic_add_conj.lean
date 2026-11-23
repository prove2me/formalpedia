-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_add_conj
-- name    : GroundTheory.Automorphic.add_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:51.397157+00:00
-- url     : https://prove2.me/theorems/427aaded-9f63-45c1-8e9c-1814ca8ed94c
-- title:
--   Automorphic: add conj
-- statement:
--   The Automorphic construction uses the add conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L149-L150

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

theorem GroundTheory.Automorphic.add_conj (x : E) : x + conj F E x = algebraMap F E (Algebra.trace F E x) := by sorry
