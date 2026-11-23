-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap
-- name    : GroundTheory.Automorphic.conj_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:21.749216+00:00
-- url     : https://prove2.me/theorems/77430bef-d5eb-405d-a933-435e3462899f
-- title:
--   Automorphic: conj algebra Map
-- statement:
--   The Automorphic construction uses the conj algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean#L146-L147

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

theorem GroundTheory.Automorphic.conj_algebraMap (c : F) : conj F E (algebraMap F E c) = algebraMap F E c := by sorry
