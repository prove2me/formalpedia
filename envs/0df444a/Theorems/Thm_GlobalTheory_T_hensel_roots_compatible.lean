-- Prove2me | Theorems.Thm_GlobalTheory_T_hensel_roots_compatible
-- name    : GlobalTheory.T.hensel_roots_compatible
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:50.160372+00:00
-- url     : https://prove2.me/theorems/e7a0a01e-c51e-4ebd-9275-b2b693df1695
-- title:
--   T: hensel roots compatible
-- statement:
--   The T construction uses the hensel roots compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HenselRootsCompatibleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HenselRootsCompatibleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatible
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatibleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hensel_roots_compatible : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V), IsLocalHom α → ∀ (θ : R) (η : V) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (q.map α).eval η = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n) → ∃ ψ : R →+* V, ψ.comp φ = α ∧ IsLocalHom ψ := by sorry
