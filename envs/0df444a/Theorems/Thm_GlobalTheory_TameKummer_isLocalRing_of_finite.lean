-- Prove2me | Theorems.Thm_GlobalTheory_TameKummer_isLocalRing_of_finite
-- name    : GlobalTheory.TameKummer.isLocalRing_of_finite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:29.243802+00:00
-- url     : https://prove2.me/theorems/55501041-4397-47a6-9d0a-69509fbf23a0
-- title:
--   Tame Kummer: is Local Ring of finite
-- statement:
--   The Tame Kummer construction uses the is Local Ring of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GaloisOfPrimePowerDegree.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GaloisOfPrimePowerDegree.lean#L73-L79

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

theorem GlobalTheory.TameKummer.isLocalRing_of_finite (R S : Type*) [CommRing R] [HenselianLocalRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by sorry
