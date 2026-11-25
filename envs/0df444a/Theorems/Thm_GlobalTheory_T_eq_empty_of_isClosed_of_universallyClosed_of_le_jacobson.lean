-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson
-- name    : GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:50.529557+00:00
-- url     : https://prove2.me/theorems/ea9a66b5-34b7-443b-a794-1230f6078ae6
-- title:
--   T: eq empty of is Closed of universally Closed of le jacobson
-- statement:
--   The T construction uses the eq empty of is Closed of universally Closed of le jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedEmptyOfUniversallyClosedOfLeJacobsonStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedEmptyOfUniversallyClosedOfLeJacobsonStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedEmptyOfUniversallyClosedOfLeJacobson
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedEmptyOfUniversallyClosedOfLeJacobsonStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by sorry
