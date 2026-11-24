-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_comp_liftBaseChange
-- name    : GlobalTheory.QCoh.isLocalizedModule_comp_liftBaseChange
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:20.963568+00:00
-- url     : https://prove2.me/theorems/13a3e4ea-0081-4b3e-a4a8-5328c84b30b4
-- title:
--   QCoh: is Localized Module comp lift Base Change
-- statement:
--   The QCoh construction uses the is Localized Module comp lift Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L339-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L339-L351

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

theorem GlobalTheory.QCoh.isLocalizedModule_comp_liftBaseChange {A B M N P : Type*} (C : Type*) [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] [AddCommGroup P] [Module A P] [Module B P] [Module C P]
    [IsScalarTower A B P] [IsScalarTower A C P] [IsScalarTower B C P]
    (l : M →ₗ[A] N) (g : N →ₗ[B] P) (S : Submonoid B) [IsLocalization S C]
    (h : IsBaseChange C (g.restrictScalars A ∘ₗ l)) :
    IsLocalizedModule S (g ∘ₗ l.liftBaseChange B) := by sorry
