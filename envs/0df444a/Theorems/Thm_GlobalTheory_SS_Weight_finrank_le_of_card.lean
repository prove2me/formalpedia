-- Prove2me | Theorems.Thm_GlobalTheory_SS_Weight_finrank_le_of_card
-- name    : GlobalTheory.SS.Weight.finrank_le_of_card
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:19.936152+00:00
-- url     : https://prove2.me/theorems/9600631e-9873-4fed-81aa-fcd96978f20c
-- title:
--   Weight: finrank le of card
-- statement:
--   The Weight construction uses the finrank le of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightLeAddOfTorsionPairing.lean#L15-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightLeAddOfTorsionPairing.lean#L15-L95

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

theorem GlobalTheory.SS.Weight.finrank_le_of_card (l : ℕ) [hl : Fact l.Prime] {T M : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] [AddCommGroup M]
    (π : ℕ → T →+ M) (hker : ∀ n x, π n x = 0 ↔ ∃ y, x = l ^ n • y)
    (hfin : ∀ n, Finite {x : M // l ^ n • x = 0})
    (U : Submodule ℤ_[l] T) (H : AddSubgroup M) (hU : ∀ n, ∀ x ∈ U, π n x ∈ H) (C k : ℕ)
    (hc : ∀ n, Nat.card {x : H // l ^ n • x = 0} ≤ C * l ^ (n * k)) :
    finrank ℤ_[l] U ≤ k := by sorry
