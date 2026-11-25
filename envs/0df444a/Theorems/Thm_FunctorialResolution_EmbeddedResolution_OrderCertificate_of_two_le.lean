-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OrderCertificate_of_two_le
-- name    : FunctorialResolution.EmbeddedResolution.OrderCertificate.of_two_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:02.466585+00:00
-- url     : https://prove2.me/theorems/218cd0f6-feaa-570b-851f-fce53047596c
-- title:
--   Order Certificate: of two le
-- statement:
--   The Order Certificate construction uses the of two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/PrincipalizationCertificate.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/PrincipalizationCertificate.lean#L101-L105

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.OrderCertificate.of_two_le {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hmu : 2 ≤ μ) :
    OrderCertificate W p N μ Mem Z := by sorry
