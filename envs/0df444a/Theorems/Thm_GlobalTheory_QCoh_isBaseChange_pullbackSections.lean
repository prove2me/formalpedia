-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isBaseChange_pullbackSections
-- name    : GlobalTheory.QCoh.isBaseChange_pullbackSections
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:03:16.811095+00:00
-- url     : https://prove2.me/theorems/b18ab2ad-45fa-4ab3-a691-ecb49be4b2ab
-- title:
--   QCoh: is Base Change pullback Sections
-- statement:
--   The QCoh construction uses the is Base Change pullback Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L428-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L428-L450

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) {U : X.Opens} {V : Y.Opens}
variable [G.IsQuasicoherent]
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.isBaseChange_pullbackSections (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    IsBaseChange Γ(X, U) (pullbackSections f G e) := by sorry
