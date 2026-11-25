-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_suppDim_eq_iSup_closure
-- name    : GlobalTheory.QCoh.suppDim_eq_iSup_closure
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:07.970868+00:00
-- url     : https://prove2.me/theorems/6f23c49b-e006-5bdd-8b7a-99b291a2dfff
-- title:
--   QCoh: supp Dim eq i Sup closure
-- statement:
--   The QCoh construction uses the supp Dim eq i Sup closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L744-L746
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L744-L746

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable (F)

theorem GlobalTheory.QCoh.suppDim_eq_iSup_closure [IsFiniteQC F] :
    suppDim F = ⨆ x ∈ support F, topologicalKrullDim (closure {x} : Set X) := by sorry
