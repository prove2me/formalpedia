-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_isSemisimpleModule_asModule
-- name    : GroundTheory.Automorphic.CompactRep.isSemisimpleModule_asModule
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:29.141542+00:00
-- url     : https://prove2.me/theorems/a7b5a6db-3f76-4c42-b8c6-3a5abbccc514
-- title:
--   Compact Rep: is Semisimple Module as Module
-- statement:
--   The Compact Rep construction uses the is Semisimple Module as Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L74-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L74-L96

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]
variable {σ : Representation ℂ K X}

theorem GroundTheory.Automorphic.CompactRep.isSemisimpleModule_asModule (h : IsKFinite σ) :
    IsSemisimpleModule (MonoidAlgebra ℂ K) σ.asModule := by sorry
