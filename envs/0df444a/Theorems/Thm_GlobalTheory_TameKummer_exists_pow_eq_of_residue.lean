-- Prove2me | Theorems.Thm_GlobalTheory_TameKummer_exists_pow_eq_of_residue
-- name    : GlobalTheory.TameKummer.exists_pow_eq_of_residue
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:27.733789+00:00
-- url     : https://prove2.me/theorems/05fa5fad-2a7c-4f2f-8d17-48b0f8ba5e95
-- title:
--   Tame Kummer: exists pow eq of residue
-- statement:
--   The Tame Kummer construction uses the exists pow eq of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GaloisOfPrimePowerDegree.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GaloisOfPrimePowerDegree.lean#L14-L31

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

theorem GlobalTheory.TameKummer.exists_pow_eq_of_residue {R : Type*} [CommRing R] [HenselianLocalRing R] {n : ℕ}
    (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u) (c : ResidueField R)
    (hc : c ^ n = residue R u) : ∃ v : R, v ^ n = u ∧ residue R v = c := by sorry
