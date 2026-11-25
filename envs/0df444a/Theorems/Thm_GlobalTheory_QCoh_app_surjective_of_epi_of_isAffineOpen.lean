-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_app_surjective_of_epi_of_isAffineOpen
-- name    : GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:02:38.164709+00:00
-- url     : https://prove2.me/theorems/9829f81c-7e59-46d6-9841-87daeab2894f
-- title:
--   QCoh: app surjective of epi of is Affine Open
-- statement:
--   The QCoh construction uses the app surjective of epi of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L542-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L542-L561

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen (φ : F ⟶ F') [Epi φ] [F.IsQuasicoherent]
    [F'.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (φ.app U) := by sorry
