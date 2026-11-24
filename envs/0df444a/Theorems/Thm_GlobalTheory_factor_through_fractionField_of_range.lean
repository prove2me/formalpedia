-- Prove2me | Theorems.Thm_GlobalTheory_factor_through_fractionField_of_range
-- name    : GlobalTheory.factor_through_fractionField_of_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:35.748242+00:00
-- url     : https://prove2.me/theorems/42809144-48ce-4e2b-830c-04f28ad5d9d0
-- title:
--   Global Theory: factor through fraction Field of range
-- statement:
--   The Global Theory construction uses the factor through fraction Field of range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FactorThroughGenericFiber.lean#L7-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FactorThroughGenericFiber.lean#L7-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FactorThroughGenericFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.factor_through_fractionField_of_range :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0})
      (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) →
        ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by sorry
