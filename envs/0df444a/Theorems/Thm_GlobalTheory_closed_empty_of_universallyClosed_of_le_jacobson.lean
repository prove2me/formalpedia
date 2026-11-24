-- Prove2me | Theorems.Thm_GlobalTheory_closed_empty_of_universallyClosed_of_le_jacobson
-- name    : GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:35.442795+00:00
-- url     : https://prove2.me/theorems/d1bbb00c-431c-4f9f-b70b-87eac58dbbcd
-- title:
--   Global Theory: closed empty of universally Closed of le jacobson
-- statement:
--   The Global Theory construction uses the closed empty of universally Closed of le jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedEmptyOfUniversallyClosedOfLeJacobson.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedEmptyOfUniversallyClosedOfLeJacobson.lean#L8-L26

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedEmptyOfUniversallyClosedOfLeJacobson
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
open GlobalTheory

theorem GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson :
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by sorry
