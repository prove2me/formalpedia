-- Prove2me | Theorems.Thm_GlobalTheory_Unipotence_root_of_unity
-- name    : GlobalTheory.Unipotence.root_of_unity
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:38.606262+00:00
-- url     : https://prove2.me/theorems/b79e2d70-2029-4f6f-9f4a-f3aa0982a41f
-- title:
--   Unipotence: root of unity
-- statement:
--   The Unipotence construction uses the root of unity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsNilpotentSubOneOfConjPow.lean#L30-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsNilpotentSubOneOfConjPow.lean#L30-L53

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

theorem GlobalTheory.Unipotence.root_of_unity {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hA : IsUnit A) (P : (Matrix n n K)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (h : (P : Matrix n n K) * A = A ^ q * P) (x : K) (hx : x ∈ spectrum K A) :
    ∃ m : ℕ, m ≠ 0 ∧ x ^ m = 1 := by sorry
