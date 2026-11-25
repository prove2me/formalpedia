-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_pullbackSections_smul
-- name    : GlobalTheory.QCoh.pullbackSections_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:02:48.5827+00:00
-- url     : https://prove2.me/theorems/7ec08ed4-e1b8-415d-b940-0fba22489a54
-- title:
--   QCoh: pullback Sections smul
-- statement:
--   The QCoh construction uses the pullback Sections smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L207-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L207-L210

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

theorem GlobalTheory.QCoh.pullbackSections_smul (e : U ≤ f ⁻¹ᵁ V) (r : Γ(Y, V)) (s : Γ(G, V)) :
    pullbackSections f G e (r • s) = f.appLE V U e r • pullbackSections f G e s := by sorry
