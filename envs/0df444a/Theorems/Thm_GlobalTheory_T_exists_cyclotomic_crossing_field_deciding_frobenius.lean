-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_cyclotomic_crossing_field_deciding_frobenius
-- name    : GlobalTheory.T.exists_cyclotomic_crossing_field_deciding_frobenius
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:02.529714+00:00
-- url     : https://prove2.me/theorems/4bc7f330-38ac-411f-add8-4401bc96c6a7
-- title:
--   T: exists cyclotomic crossing field deciding frobenius
-- statement:
--   The T construction uses the exists cyclotomic crossing field deciding frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobeniusStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobeniusStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicCrossingFieldDecidingFrobenius
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicCrossingFieldDecidingFrobeniusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_cyclotomic_crossing_field_deciding_frobenius : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by sorry
