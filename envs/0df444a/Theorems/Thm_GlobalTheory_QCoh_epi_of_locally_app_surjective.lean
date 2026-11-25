-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_epi_of_locally_app_surjective
-- name    : GlobalTheory.QCoh.epi_of_locally_app_surjective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:03:38.32307+00:00
-- url     : https://prove2.me/theorems/d381a9d3-da9e-4f80-ab41-558e8941d4b8
-- title:
--   QCoh: epi of locally app surjective
-- statement:
--   The QCoh construction uses the epi of locally app surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L527-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L527-L538

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
variable {X Y : Scheme.{u}} {F F' : X.Modules}

theorem GlobalTheory.QCoh.epi_of_locally_app_surjective (φ : F ⟶ F')
    (h : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
      Function.Surjective (φ.app U)) : Epi φ := by sorry
