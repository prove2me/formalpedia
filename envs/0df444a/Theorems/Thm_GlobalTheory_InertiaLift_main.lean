-- Prove2me | Theorems.Thm_GlobalTheory_InertiaLift_main
-- name    : GlobalTheory.InertiaLift.main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:14.145326+00:00
-- url     : https://prove2.me/theorems/e581f4c8-2e08-508a-8a85-4c49281add0e
-- title:
--   Inertia Lift: main
-- statement:
--   The Inertia Lift construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L169-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L169-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteGaloisInertiaLiftsAbsoluteInertiaRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise
open GlobalTheory GlobalTheory.InertiaLift
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem GlobalTheory.InertiaLift.main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by sorry
