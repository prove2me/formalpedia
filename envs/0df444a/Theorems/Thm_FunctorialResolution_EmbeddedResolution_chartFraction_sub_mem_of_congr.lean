-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartFraction_sub_mem_of_congr
-- name    : FunctorialResolution.EmbeddedResolution.chartFraction_sub_mem_of_congr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:57.177405+00:00
-- url     : https://prove2.me/theorems/acc1bc42-f098-4f7f-9eb4-9e9f2ad544b2
-- title:
--   Embedded Resolution: chart Fraction sub mem of congr
-- statement:
--   The Embedded Resolution construction uses the chart Fraction sub mem of congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L193-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L193-L224

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

theorem FunctorialResolution.EmbeddedResolution.chartFraction_sub_mem_of_congr {A : Type u} [CommRing A] (I : Ideal R) (a : I)
    (φ φ' : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a) →+* A)
    (σ σ' : R →+* A) (𝔟 : Ideal A)
    (hφ : ∀ r : R, φ (Blowup.chartRingHom I a r) = σ r)
    (hφ' : ∀ r : R, φ' (Blowup.chartRingHom I a r) = σ' r)
    (hcongr : ∀ r : R, σ r - σ' r ∈ Ideal.span {σ (a : R)} * 𝔟)
    (hnzd : σ (a : R) ∈ nonZeroDivisors A)
    (u : A) (hu : σ' (a : R) = u * σ (a : R)) (b : I) :
    φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b) ∈ 𝔟 := by sorry
