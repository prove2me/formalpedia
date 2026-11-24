-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_galois_contains_roots_of_units
-- name    : GlobalTheory.T.exists_finite_galois_contains_roots_of_units
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:18.228377+00:00
-- url     : https://prove2.me/theorems/8b22f931-9b68-473c-8d8a-609fb1e6d143
-- title:
--   T: exists finite galois contains roots of units
-- statement:
--   The T construction uses the exists finite galois contains roots of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFiniteGaloisContainsRootsOfUnitsStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFiniteGaloisContainsRootsOfUnitsStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFiniteGaloisContainsRootsOfUnits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFiniteGaloisContainsRootsOfUnitsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_galois_contains_roots_of_units : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by sorry
