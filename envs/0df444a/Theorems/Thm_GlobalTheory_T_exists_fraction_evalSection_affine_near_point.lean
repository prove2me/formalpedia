-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_fraction_evalSection_affine_near_point
-- name    : GlobalTheory.T.exists_fraction_evalSection_affine_near_point
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:05.715739+00:00
-- url     : https://prove2.me/theorems/d801e66b-5c97-4e99-8dda-7edaef95f936
-- title:
--   T: exists fraction eval Section affine near point
-- statement:
--   The T construction uses the exists fraction eval Section affine near point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFractionEvalSectionAffineNearPointStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFractionEvalSectionAffineNearPointStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_fraction_evalSection_affine_near_point : ∀ (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W)) (x : PrimeSpectrum R), x ∈ W → ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W), WtRat.ev (spMap e) W h s * e β = e α := by sorry
