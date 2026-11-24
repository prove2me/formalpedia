-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
-- name    : GlobalTheory.isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:47.46785+00:00
-- url     : https://prove2.me/theorems/12362461-3ef5-4227-ad9b-9672e8cb0be8
-- title:
--   Global Theory: is Iso of is Proper of exists Unique field point of is Integral
-- statement:
--   The Global Theory construction uses the is Iso of is Proper of exists Unique field point of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg.lean#L71-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.isIso_of_isProper_of_existsUnique_field_point_of_isIntegral {S T : Scheme.{0}} (f : S ⟶ T)
    [IsProper f] [IsReduced S] [IsIntegral T] [GlobalTheory.IsNormalScheme T]
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by sorry
