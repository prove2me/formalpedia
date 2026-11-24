-- Prove2me | Theorems.Thm_GlobalTheory_Unipotence_pow_card_eq_zero
-- name    : GlobalTheory.Unipotence.pow_card_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:35.631953+00:00
-- url     : https://prove2.me/theorems/d0f48c90-34b1-46eb-ab6c-4796db8c14ea
-- title:
--   Unipotence: pow card eq zero
-- statement:
--   The Unipotence construction uses the pow card eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsNilpotentSubOneOfConjPow.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsNilpotentSubOneOfConjPow.lean#L15-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.Unipotence
open Polynomial

theorem GlobalTheory.Unipotence.pow_card_eq_zero {K n : Type} [Field K] [IsAlgClosed K] [Fintype n] [DecidableEq n]
    (Y : Matrix n n K) (h : ∀ μ ∈ spectrum K Y, μ = 0) : IsNilpotent Y := by sorry
