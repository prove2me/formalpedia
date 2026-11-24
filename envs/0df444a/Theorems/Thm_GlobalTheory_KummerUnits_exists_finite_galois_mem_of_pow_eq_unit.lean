-- Prove2me | Theorems.Thm_GlobalTheory_KummerUnits_exists_finite_galois_mem_of_pow_eq_unit
-- name    : GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:03.561796+00:00
-- url     : https://prove2.me/theorems/1296d632-9299-4033-8225-1ffdbed06946
-- title:
--   Kummer Units: exists finite galois mem of pow eq unit
-- statement:
--   The Kummer Units construction uses the exists finite galois mem of pow eq unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFiniteGaloisContainsRootsOfUnits.lean#L6-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFiniteGaloisContainsRootsOfUnits.lean#L6-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFiniteGaloisContainsRootsOfUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.KummerUnits

theorem GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by sorry
