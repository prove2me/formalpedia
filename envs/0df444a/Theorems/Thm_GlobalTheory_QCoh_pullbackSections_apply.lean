-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_pullbackSections_apply
-- name    : GlobalTheory.QCoh.pullbackSections_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:02:58.903851+00:00
-- url     : https://prove2.me/theorems/e19998b0-e1e4-454c-8899-805a82a2ce03
-- title:
--   QCoh: pullback Sections apply
-- statement:
--   The QCoh construction uses the pullback Sections apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L203-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L203-L205

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

theorem GlobalTheory.QCoh.pullbackSections_apply (e : U ≤ f ⁻¹ᵁ V) (s : Γ(G, V)) :
    pullbackSections f G e s = ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s) := by sorry
