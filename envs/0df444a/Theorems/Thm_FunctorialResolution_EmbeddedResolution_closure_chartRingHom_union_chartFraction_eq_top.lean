-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_chartRingHom_union_chartFraction_eq_top
-- name    : FunctorialResolution.EmbeddedResolution.closure_chartRingHom_union_chartFraction_eq_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:12.755269+00:00
-- url     : https://prove2.me/theorems/c788db44-e1cb-4652-8024-3a04844b3bc3
-- title:
--   Embedded Resolution: closure chart Ring Hom union chart Fraction eq top
-- statement:
--   The Embedded Resolution construction uses the closure chart Ring Hom union chart Fraction eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L171-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L171-L191

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {R : Type u} [CommRing R]

theorem FunctorialResolution.EmbeddedResolution.closure_chartRingHom_union_chartFraction_eq_top (I : Ideal R) (a : I) :
    Subring.closure
        (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)) = ⊤ := by sorry
