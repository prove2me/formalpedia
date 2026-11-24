-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_irreducibleComponents_not_subset_support_comap
-- name    : FunctorialResolution.EmbeddedResolution.irreducibleComponents_not_subset_support_comap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:06:48.154046+00:00
-- url     : https://prove2.me/theorems/16edde60-b8a2-4f01-8b71-f0056858bd73
-- title:
--   Embedded Resolution: irreducible Components not subset support comap
-- statement:
--   The Embedded Resolution construction uses the irreducible Components not subset support comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L64-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L64-L129

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingFlatPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.irreducibleComponents_not_subset_support_comap (h : Y ⟶ X) (hg : GeneralizingMap (fun y : Y => h.base y))
    (E : List X.IdealSheafData) (N : X.IdealSheafData)
    (hN : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
      (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ (N.support : Set X)) :
    ∀ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), ∀ C : Set Y, IsIrreducible C →
      C ⊆ (D.support : Set Y) →
      (∀ C' : Set Y, IsIrreducible C' → C' ⊆ (D.support : Set Y) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ ((N.comap h).support : Set Y) := by sorry
