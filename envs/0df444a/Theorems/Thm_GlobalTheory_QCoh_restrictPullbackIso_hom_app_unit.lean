-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_restrictPullbackIso_hom_app_unit
-- name    : GlobalTheory.QCoh.restrictPullbackIso_hom_app_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:02:09.137951+00:00
-- url     : https://prove2.me/theorems/197c93c3-5a55-5c62-a125-c9f80a2d7069
-- title:
--   QCoh: restrict Pullback Iso hom app unit
-- statement:
--   The QCoh construction uses the restrict Pullback Iso hom app unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L351-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L351-L366

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

theorem GlobalTheory.QCoh.restrictPullbackIso_hom_app_unit (G : Y.Modules) (V : Y.Opens) (s : Γ(G, V)) :
    ((restrictPullbackIso w).hom.app G).app (j ⁻¹ᵁ f ⁻¹ᵁ V)
      (((Scheme.Modules.pullback p).obj (G.restrict i)).presheaf.map
        (eqToHom (show j ⁻¹ᵁ f ⁻¹ᵁ V = p ⁻¹ᵁ i ⁻¹ᵁ V by
          rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage])).op
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (G.restrict i)).app (i ⁻¹ᵁ V)
          (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s))) =
    ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE (j.image_preimage_le (f ⁻¹ᵁ V))).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s) := by sorry
