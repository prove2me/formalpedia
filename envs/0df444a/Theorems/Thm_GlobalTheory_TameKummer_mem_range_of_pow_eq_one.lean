-- Prove2me | Theorems.Thm_GlobalTheory_TameKummer_mem_range_of_pow_eq_one
-- name    : GlobalTheory.TameKummer.mem_range_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:23.021076+00:00
-- url     : https://prove2.me/theorems/74a324e4-fb0d-4481-bfe4-88d8d1c35939
-- title:
--   Tame Kummer: mem range of pow eq one
-- statement:
--   The Tame Kummer construction uses the mem range of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GaloisOfPrimePowerDegree.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GaloisOfPrimePowerDegree.lean#L95-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TameKummer
open IsLocalRing Polynomial

theorem GlobalTheory.TameKummer.mem_range_of_pow_eq_one {R : Type*} (K : Type*) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
    (hn : IsUnit (n : R)) {Ω : Type*} [Field Ω] [Algebra K Ω] {ζ : Ω} (hζ : ζ ^ n = 1) :
    ζ ∈ Set.range (algebraMap K Ω) := by sorry
