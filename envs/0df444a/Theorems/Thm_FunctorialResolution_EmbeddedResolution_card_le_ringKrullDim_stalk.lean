-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_card_le_ringKrullDim_stalk
-- name    : FunctorialResolution.EmbeddedResolution.card_le_ringKrullDim_stalk
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:14.250899+00:00
-- url     : https://prove2.me/theorems/6f36a15f-f825-5e8f-8a70-1dfe18df378c
-- title:
--   Embedded Resolution: card le ring Krull Dim stalk
-- statement:
--   The Embedded Resolution construction uses the card le ring Krull Dim stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateDimensionBound.lean#L57-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateDimensionBound.lean#L57-L87

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateDimensionBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem FunctorialResolution.EmbeddedResolution.card_le_ringKrullDim_stalk (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    (J.card : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by sorry
