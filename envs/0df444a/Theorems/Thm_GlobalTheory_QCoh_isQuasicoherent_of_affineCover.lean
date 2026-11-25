-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_affineCover
-- name    : GlobalTheory.QCoh.isQuasicoherent_of_affineCover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:52.736077+00:00
-- url     : https://prove2.me/theorems/2ca94d7b-6931-4349-b31b-be1c1cdad8bc
-- title:
--   QCoh: is Quasicoherent of affine Cover
-- statement:
--   The QCoh construction uses the is Quasicoherent of affine Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L218-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L218-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.isQuasicoherent_of_affineCover {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i))
    (h : ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f)) :
    F.IsQuasicoherent := by sorry
