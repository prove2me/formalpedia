-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_conj_apply
-- name    : GroundTheory.Automorphic.conj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:18.221302+00:00
-- url     : https://prove2.me/theorems/e041d9f0-20d6-4ed3-98cb-6433cc79f2b4
-- title:
--   Automorphic: conj apply
-- statement:
--   The Automorphic construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L141-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L141-L141

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

theorem GroundTheory.Automorphic.conj_apply (x : E) : conj F E x = algebraMap F E (Algebra.trace F E x) - x := by sorry
