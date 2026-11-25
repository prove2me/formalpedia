-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mono_of_locally_app_injective
-- name    : GlobalTheory.QCoh.mono_of_locally_app_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:16.822497+00:00
-- url     : https://prove2.me/theorems/1dad4c30-33c1-4306-9378-65e81f8c4594
-- title:
--   QCoh: mono of locally app injective
-- statement:
--   The QCoh construction uses the mono of locally app injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L515-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L515-L525

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

theorem GlobalTheory.QCoh.mono_of_locally_app_injective (φ : F ⟶ F')
    (h : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
      Function.Injective (φ.app U)) : Mono φ := by sorry
