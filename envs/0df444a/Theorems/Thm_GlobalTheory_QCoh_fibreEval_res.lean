-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_fibreEval_res
-- name    : GlobalTheory.QCoh.fibreEval_res
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:12.51479+00:00
-- url     : https://prove2.me/theorems/388452d9-4592-4d82-a437-39f77fd8e999
-- title:
--   QCoh: fibre Eval res
-- statement:
--   The QCoh construction uses the fibre Eval res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1068-L1070
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1068-L1070

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

theorem GlobalTheory.QCoh.fibreEval_res (h : V ≤ U) (x : V) (s : Γ(F, U)) :
    fibreEval F x (F.presheaf.map (homOfLE h).op s) = fibreEval F (⟨x, h x.2⟩ : U) s := by sorry
