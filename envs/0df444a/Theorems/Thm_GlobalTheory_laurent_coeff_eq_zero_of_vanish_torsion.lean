-- Prove2me | Theorems.Thm_GlobalTheory_laurent_coeff_eq_zero_of_vanish_torsion
-- name    : GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:20.364246+00:00
-- url     : https://prove2.me/theorems/00b824eb-1890-40f8-946e-944a3a6b2b8b
-- title:
--   Global Theory: laurent coeff eq zero of vanish torsion
-- statement:
--   The Global Theory construction uses the laurent coeff eq zero of vanish torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffEqZeroOfSumSmulEqZeroOfSeparating.lean#L43-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffEqZeroOfSumSmulEqZeroOfSeparating.lean#L43-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffEqZeroOfSumSmulEqZeroOfSeparating
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion :
    ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (n : ℕ), n.Prime →
    ∀ s : Finset Y, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (A : Type) [CommRing A] [IsLocalRing A] (ζ : A),
    IsUnit (n : A) → ζ ^ (n ^ j) = 1 → IsPrimitiveRoot (IsLocalRing.residue A ζ) (n ^ j) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] (a : Y → M),
    (∀ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) →
      ∑ y ∈ s, (t (Multiplicative.ofAdd y) : A) • a y = 0) → ∀ y ∈ s, a y = 0 := by sorry
