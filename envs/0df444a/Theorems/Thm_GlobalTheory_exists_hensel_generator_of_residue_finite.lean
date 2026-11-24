-- Prove2me | Theorems.Thm_GlobalTheory_exists_hensel_generator_of_residue_finite
-- name    : GlobalTheory.exists_hensel_generator_of_residue_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:36.719409+00:00
-- url     : https://prove2.me/theorems/3ec71c45-1c4a-4a41-8807-ef769b9168d2
-- title:
--   Global Theory: exists hensel generator of residue finite
-- statement:
--   The Global Theory construction uses the exists hensel generator of residue finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimitiveElementComplete.lean#L14-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimitiveElementComplete.lean#L14-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimitiveElementComplete
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

theorem GlobalTheory.exists_hensel_generator_of_residue_finite : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], (ResidueField.map φ).Finite → CharZero (ResidueField A) → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by sorry
