-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_isLocalizedModule_of_ringHom_of_qcqs
-- name    : GlobalTheory.QCoh.Qcqs.isLocalizedModule_of_ringHom_of_qcqs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:50.680623+00:00
-- url     : https://prove2.me/theorems/7c496058-862e-498d-9c5d-63b6fead0f1d
-- title:
--   Qcqs: is Localized Module of ring Hom of qcqs
-- statement:
--   The Qcqs construction uses the is Localized Module of ring Hom of qcqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L216-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L216-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable [F.IsQuasicoherent]

theorem GlobalTheory.QCoh.Qcqs.isLocalizedModule_of_ringHom_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) {A : Type*} [CommRing A]
    (φ : A →+* Γ(X, U)) (a : A) (h : V ≤ U) (hV : V = X.basicOpen (φ a))
    [Module A Γ(F, U)] [Module A Γ(F, V)]
    (hsU : ∀ (r : A) (s : Γ(F, U)), r • s = φ r • s)
    (hsV : ∀ (r : A) (s : Γ(F, V)), r • s = X.presheaf.map (homOfLE h).op (φ r) • s)
    (l : Γ(F, U) →ₗ[A] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsLocalizedModule.Away a l := by sorry
