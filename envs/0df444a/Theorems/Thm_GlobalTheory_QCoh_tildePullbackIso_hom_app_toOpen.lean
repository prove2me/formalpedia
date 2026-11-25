-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_tildePullbackIso_hom_app_toOpen
-- name    : GlobalTheory.QCoh.tildePullbackIso_hom_app_toOpen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:02:04.218803+00:00
-- url     : https://prove2.me/theorems/1f25c5d2-fdfe-53b4-8b3d-0467c19dc599
-- title:
--   QCoh: tilde Pullback Iso hom app to Open
-- statement:
--   The QCoh construction uses the tilde Pullback Iso hom app to Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L290-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L290-L300

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
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.tildePullbackIso_hom_app_toOpen (M : ModuleCat.{u} R) (m : M) :
    ((tildePullbackIso φ).hom.app M).app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
      (tilde.toOpen M ⊤ m) := by sorry
