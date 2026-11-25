-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_pullback_map_app_pullbackSections
-- name    : GlobalTheory.QCoh.pullback_map_app_pullbackSections
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:27.542054+00:00
-- url     : https://prove2.me/theorems/2579da5f-4480-47c0-bcd5-03e2df124abb
-- title:
--   QCoh: pullback map app pullback Sections
-- statement:
--   The QCoh construction uses the pullback map app pullback Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L224-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L224-L231

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
variable (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) {U U' : X.Opens} {V V' : Y.Opens}

theorem GlobalTheory.QCoh.pullback_map_app_pullbackSections {G G' : Y.Modules} (φ : G ⟶ G') (e : U ≤ f ⁻¹ᵁ V)
    (s : Γ(G, V)) :
    ((Scheme.Modules.pullback f).map φ).app U (pullbackSections f G e s) =
      pullbackSections f G' e (φ.app V s) := by sorry
