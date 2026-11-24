-- Prove2me | Theorems.Thm_GlobalTheory_exists_hensel_generator_of_residue_finite_unramified
-- name    : GlobalTheory.exists_hensel_generator_of_residue_finite_unramified
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:42.326449+00:00
-- url     : https://prove2.me/theorems/10afe7b8-c6ca-4003-8f89-2357baf0406e
-- title:
--   Global Theory: exists hensel generator of residue finite unramified
-- statement:
--   The Global Theory construction uses the exists hensel generator of residue finite unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimitiveElementUnramified.lean#L16-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimitiveElementUnramified.lean#L16-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimitiveElementUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open IsLocalRing Polynomial

theorem GlobalTheory.exists_hensel_generator_of_residue_finite_unramified : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], ((residue R).comp φ).Finite → ((residue R).comp φ).FormallyUnramified → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by sorry
