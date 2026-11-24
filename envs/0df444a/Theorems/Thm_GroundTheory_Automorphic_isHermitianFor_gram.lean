-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isHermitianFor_gram
-- name    : GroundTheory.Automorphic.isHermitianFor_gram
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:14.824053+00:00
-- url     : https://prove2.me/theorems/27d514a8-fcee-4de1-a9ac-4c4955278b34
-- title:
--   Automorphic: is Hermitian For gram
-- statement:
--   The Automorphic construction uses the is Hermitian For gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L117-L121

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
omit [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.isHermitianFor_gram (h : HermitianForm F E V) (v : Basis ι E V) :
    IsHermitianFor (conjHom F E) (gram h.toSesq v) := by sorry
