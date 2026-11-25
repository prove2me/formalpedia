-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isBaseChange_fibreEval
-- name    : GlobalTheory.QCoh.isBaseChange_fibreEval
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:39.827796+00:00
-- url     : https://prove2.me/theorems/c4dfcea8-8850-4b8e-94bf-986926b94fab
-- title:
--   QCoh: is Base Change fibre Eval
-- statement:
--   The QCoh construction uses the is Base Change fibre Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1074-L1076
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1074-L1076

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

theorem GlobalTheory.QCoh.isBaseChange_fibreEval [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsBaseChange (X.residueField (x : X)) (fibreEval F x) := by sorry
