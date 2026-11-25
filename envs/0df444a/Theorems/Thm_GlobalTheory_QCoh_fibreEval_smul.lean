-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_fibreEval_smul
-- name    : GlobalTheory.QCoh.fibreEval_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:29.570931+00:00
-- url     : https://prove2.me/theorems/869a4f6b-108c-455d-bf59-02d80fdba7c9
-- title:
--   QCoh: fibre Eval smul
-- statement:
--   The QCoh construction uses the fibre Eval smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1064-L1066
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1064-L1066

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

theorem GlobalTheory.QCoh.fibreEval_smul (x : U) (f : Γ(X, U)) (s : Γ(F, U)) :
    fibreEval F x (f • s) = X.evaluation U x x.2 f • fibreEval F x s := by sorry
