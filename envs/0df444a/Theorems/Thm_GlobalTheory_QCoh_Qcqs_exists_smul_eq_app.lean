-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_smul_eq_app
-- name    : GlobalTheory.QCoh.Qcqs.exists_smul_eq_app
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:27.094077+00:00
-- url     : https://prove2.me/theorems/6a3819db-2468-4c9b-934d-5910a3bf49ef
-- title:
--   Qcqs: exists smul eq app
-- statement:
--   The Qcqs construction uses the exists smul eq app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L279-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L279-L303

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
variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}

theorem GlobalTheory.QCoh.Qcqs.exists_smul_eq_app (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (S : Submonoid Γ(X, U))
    (hker : ∀ (V : X.Opens) (h : V ≤ U), IsAffineOpen V → ∀ a : Γ(F, V), φ.app V a = 0 →
      ∃ s ∈ S, X.presheaf.map (homOfLE h).op s • a = 0)
    (hsurj : ∀ (V : X.Opens) (h : V ≤ U), IsAffineOpen V → ∀ b : Γ(G, V),
      ∃ s ∈ S, ∃ a : Γ(F, V), X.presheaf.map (homOfLE h).op s • b = φ.app V a)
    (b : Γ(G, U)) : ∃ s ∈ S, ∃ a : Γ(F, U), s • b = φ.app U a := by sorry
