-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_field_point_morphismRestrict
-- name    : GlobalTheory.existsUnique_field_point_morphismRestrict
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:04.65587+00:00
-- url     : https://prove2.me/theorems/2b2f3173-fbf5-42ae-81a2-88719247dc21
-- title:
--   Global Theory: exists Unique field point morphism Restrict
-- statement:
--   The Global Theory construction uses the exists Unique field point morphism Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg.lean#L31-L42

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

theorem GlobalTheory.existsUnique_field_point_morphismRestrict {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) (V : T.Opens)
    (k : Type) [Field k] (w : Sp k ⟶ V) : ∃! z : Sp k ⟶ (f ⁻¹ᵁ V), z ≫ (f ∣_ V) = w := by sorry
