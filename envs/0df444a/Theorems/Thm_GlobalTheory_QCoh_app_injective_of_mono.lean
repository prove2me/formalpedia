-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_app_injective_of_mono
-- name    : GlobalTheory.QCoh.app_injective_of_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:55.571008+00:00
-- url     : https://prove2.me/theorems/7702f8d1-2b07-5410-a115-6caec20d4001
-- title:
--   QCoh: app injective of mono
-- statement:
--   The QCoh construction uses the app injective of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L508-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L508-L513

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

theorem GlobalTheory.QCoh.app_injective_of_mono (φ : F ⟶ F') [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) := by sorry
