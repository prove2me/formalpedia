-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_restrictPullbackIso_hom_app_pullbackSections
-- name    : GlobalTheory.QCoh.restrictPullbackIso_hom_app_pullbackSections
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:01:57.96482+00:00
-- url     : https://prove2.me/theorems/d90ad587-5ae6-5331-be7c-b6f9f1c750b8
-- title:
--   QCoh: restrict Pullback Iso hom app pullback Sections
-- statement:
--   The QCoh construction uses the restrict Pullback Iso hom app pullback Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L370-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L370-L396

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
variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {p : X' ⟶ Y'} {j : X' ⟶ X} {i : Y' ⟶ Y}
  [IsOpenImmersion i] [IsOpenImmersion j] (w : p ≫ i = j ≫ f)
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.restrictPullbackIso_hom_app_pullbackSections (G : Y.Modules) {V : Y.Opens} {V' : Y'.Opens}
    {U' : X'.Opens} (hV : i ''ᵁ V' ≤ V) (e' : U' ≤ p ⁻¹ᵁ V') (e : j ''ᵁ U' ≤ f ⁻¹ᵁ V)
    (s : Γ(G, V)) :
    ((restrictPullbackIso w).hom.app G).app U'
      (pullbackSections p (G.restrict i) e' (G.presheaf.map (homOfLE hV).op s)) =
    pullbackSections f G e s := by sorry
