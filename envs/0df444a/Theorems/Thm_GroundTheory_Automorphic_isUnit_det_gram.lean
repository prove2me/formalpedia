-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isUnit_det_gram
-- name    : GroundTheory.Automorphic.isUnit_det_gram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:44.274361+00:00
-- url     : https://prove2.me/theorems/ab12ab3b-c342-47c7-baed-87061784f55a
-- title:
--   Automorphic: is Unit det gram
-- statement:
--   The Automorphic construction uses the is Unit det gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L123-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L123-L133

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable (V : Type*) [AddCommGroup V] [Module E V]
variable {F E V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.isUnit_det_gram (h : HermitianForm F E V) (v : Basis ι E V) :
    IsUnit (gram h.toSesq v).det := by sorry
