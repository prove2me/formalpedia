-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_pullbackSections_res
-- name    : GlobalTheory.QCoh.pullbackSections_res
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:52:49.645806+00:00
-- url     : https://prove2.me/theorems/0f63c3a7-a135-55ad-bffd-1311fe11ed2f
-- title:
--   QCoh: pullback Sections res
-- statement:
--   The QCoh construction uses the pullback Sections res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L217-L222

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

theorem GlobalTheory.QCoh.pullbackSections_res (e : U ≤ f ⁻¹ᵁ V') (h : V' ≤ V) (s : Γ(G, V)) :
    pullbackSections f G e (G.presheaf.map (homOfLE h).op s) =
      pullbackSections f G (e.trans (f.preimage_mono h)) s := by sorry
