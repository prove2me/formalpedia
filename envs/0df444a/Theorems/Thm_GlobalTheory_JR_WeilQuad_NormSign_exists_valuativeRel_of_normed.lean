-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_exists_valuativeRel_of_normed
-- name    : GlobalTheory.JR.WeilQuad.NormSign.exists_valuativeRel_of_normed
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:07:39.038899+00:00
-- url     : https://prove2.me/theorems/dd348266-98a9-41ac-a792-77cf70179841
-- title:
--   Norm Sign: exists valuative Rel of normed
-- statement:
--   The Norm Sign construction uses the exists valuative Rel of normed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormGroupSignMulAndNegOne.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormGroupSignMulAndNegOne.lean#L15-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NegOneMemNormOfValuationEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NormSign

theorem GlobalTheory.JR.WeilQuad.NormSign.exists_valuativeRel_of_normed : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F],
    ∃ _ : ValuativeRel F, IsNonarchimedeanLocalField F ∧ ∀ x y : F, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by sorry
