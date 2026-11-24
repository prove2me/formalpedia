-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OrderCertificate_comap_of_isOpenImmersion
-- name    : FunctorialResolution.EmbeddedResolution.OrderCertificate.comap_of_isOpenImmersion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:13:56.446326+00:00
-- url     : https://prove2.me/theorems/a135b30b-dd20-401c-bd58-30718d9fd768
-- title:
--   Order Certificate: comap of is Open Immersion
-- statement:
--   The Order Certificate construction uses the comap of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/CertificateOpenRestriction.lean#L432-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/CertificateOpenRestriction.lean#L432-L438

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_CertificateOpenRestriction
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

theorem FunctorialResolution.EmbeddedResolution.OrderCertificate.comap_of_isOpenImmersion {k : Type u} [Field k]
    (hin : OpenImmersionStability k) {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    {V : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    OrderCertificate V (f ≫ p) (N.comap f) μ (f.base ⁻¹' Mem) (Z.comap f) := by sorry
