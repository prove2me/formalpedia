-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_sectionsRingHom_sub_mem_ideal
-- name    : FunctorialResolution.EmbeddedResolution.sectionsRingHom_sub_mem_ideal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:33.772022+00:00
-- url     : https://prove2.me/theorems/1147796f-9e1a-4c46-9645-578ceaffc404
-- title:
--   Embedded Resolution: sections Ring Hom sub mem ideal
-- statement:
--   The Embedded Resolution construction uses the sections Ring Hom sub mem ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L268-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L268-L282

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

theorem FunctorialResolution.EmbeddedResolution.sectionsRingHom_sub_mem_ideal {A : Type u} [CommRing A] {W : Scheme.{u}}
    (ρ ρ' : W ⟶ Spec (CommRingCat.of A)) (𝔞 : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (V : W.affineOpens) (r : A) :
    Blowup.sectionsRingHom ρ (V : W.Opens) r - Blowup.sectionsRingHom ρ' (V : W.Opens) r ∈ 𝔞.ideal V := by sorry
