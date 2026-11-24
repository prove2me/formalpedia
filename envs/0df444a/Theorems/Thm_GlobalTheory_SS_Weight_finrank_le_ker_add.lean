-- Prove2me | Theorems.Thm_GlobalTheory_SS_Weight_finrank_le_ker_add
-- name    : GlobalTheory.SS.Weight.finrank_le_ker_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:18.401868+00:00
-- url     : https://prove2.me/theorems/c333d7fa-7b19-47ac-acb2-06ade3d37553
-- title:
--   Weight: finrank le ker add
-- statement:
--   The Weight construction uses the finrank le ker add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightLeAddOfTorsionPairing.lean#L97-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightLeAddOfTorsionPairing.lean#L97-L222

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors

theorem GlobalTheory.SS.Weight.finrank_le_ker_add (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (B : LinearMap.BilinForm ℤ_[l] T) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hsk : ∀ x y, B y x = - B x y) (S Φ : T ≃ₗ[ℤ_[l]] T) (q : ℕ) (hq : 2 ≤ q)
    (hN : IsNilpotent ((S : T →ₗ[ℤ_[l]] T) - 1)) (hS : ∀ x y, B (S x) (S y) = B x y)
    (hΦ : ∀ x y, B (Φ x) (Φ y) = q * B x y) (hc : Φ * S = S ^ q * Φ)
    (W : Submodule ℤ_[l] T) (P : Polynomial ℤ)
    (hP : ∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) (hW : ∀ x ∈ W, Φ x = q • x)
    (c : ℕ) (hc0 : c ≠ 0)
    (hPW : ∀ x, S x = x →
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j • (Φ^[j] (c • x)) ∈ W) :
    finrank ℤ_[l] T ≤ finrank ℤ_[l] (LinearMap.ker ((S : T →ₗ[ℤ_[l]] T) - 1)) +
      finrank ℤ_[l] W := by sorry
