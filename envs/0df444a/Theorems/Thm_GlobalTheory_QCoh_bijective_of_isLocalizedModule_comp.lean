-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_bijective_of_isLocalizedModule_comp
-- name    : GlobalTheory.QCoh.bijective_of_isLocalizedModule_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:01.956269+00:00
-- url     : https://prove2.me/theorems/5f618f27-4125-45c5-b4f5-a04aaa4236f4
-- title:
--   QCoh: bijective of is Localized Module comp
-- statement:
--   The QCoh construction uses the bijective of is Localized Module comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L326-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L326-L337

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

theorem GlobalTheory.QCoh.bijective_of_isLocalizedModule_comp {B M N : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [AddCommGroup N] [Module B N] (φ : M →ₗ[B] N) (s : Set B)
    (hs : Ideal.span s = ⊤) (P : s → Type*) [∀ b, AddCommGroup (P b)] [∀ b, Module B (P b)]
    (g : ∀ b, N →ₗ[B] P b) [∀ b : s, IsLocalizedModule.Away b.1 (g b)]
    [∀ b : s, IsLocalizedModule.Away b.1 (g b ∘ₗ φ)] : Function.Bijective φ := by sorry
