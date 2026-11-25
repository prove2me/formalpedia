-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_mk_eq_mk
-- name    : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.mk_eq_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:53:16.591833+00:00
-- url     : https://prove2.me/theorems/169a6656-3aa8-4e02-a7ff-d48d99d8f1a6
-- title:
--   Marked Ideal With Boundary: mk eq mk
-- statement:
--   The Marked Ideal With Boundary construction uses the mk eq mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L70-L77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
attribute [instance] MarkedIdealWithBoundary.instField

theorem FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.mk_eq_mk {k : Type u} [instk : Field k] (X : Scheme.{u}) (m : ℕ)
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData}
    {E E' : List X.IdealSheafData} (hp : p = p') (hI : I = I') (hE : E = E') :
    @MarkedIdealWithBoundary.mk k instk X p I m E = @MarkedIdealWithBoundary.mk k instk X p' I' m E' := by sorry
