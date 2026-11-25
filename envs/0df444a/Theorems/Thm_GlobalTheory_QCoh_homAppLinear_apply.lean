-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_homAppLinear_apply
-- name    : GlobalTheory.QCoh.homAppLinear_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:39.891091+00:00
-- url     : https://prove2.me/theorems/4523434b-74e3-5830-a5e4-cda4e2b24b42
-- title:
--   QCoh: hom App Linear apply
-- statement:
--   The QCoh construction uses the hom App Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L166-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L166-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}}

theorem GlobalTheory.QCoh.homAppLinear_apply {F F' : X.Modules} (φ : F ⟶ F') (U : X.Opens) (s : Γ(F, U)) :
    homAppLinear φ U s = φ.app U s := by sorry

attribute [defeq] GlobalTheory.QCoh.homAppLinear_apply
