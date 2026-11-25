-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_of_ringHom
-- name    : GlobalTheory.QCoh.isLocalizedModule_of_ringHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:50.543065+00:00
-- url     : https://prove2.me/theorems/8f029835-fbde-51b5-a258-d6e99df160f5
-- title:
--   QCoh: is Localized Module of ring Hom
-- statement:
--   The QCoh construction uses the is Localized Module of ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L303-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L303-L320

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
variable [F.IsQuasicoherent]

theorem GlobalTheory.QCoh.isLocalizedModule_of_ringHom (hU : IsAffineOpen U) {A : Type*} [CommRing A]
    (φ : A →+* Γ(X, U)) (a : A) (h : V ≤ U) (hV : V = X.basicOpen (φ a))
    [Module A Γ(F, U)] [Module A Γ(F, V)]
    (hsU : ∀ (r : A) (s : Γ(F, U)), r • s = φ r • s)
    (hsV : ∀ (r : A) (s : Γ(F, V)), r • s = X.presheaf.map (homOfLE h).op (φ r) • s)
    (l : Γ(F, U) →ₗ[A] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsLocalizedModule.Away a l := by sorry
