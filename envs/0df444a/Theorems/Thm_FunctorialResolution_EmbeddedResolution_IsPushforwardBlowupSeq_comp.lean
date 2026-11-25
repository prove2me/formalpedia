-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPushforwardBlowupSeq_comp
-- name    : FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:30.828328+00:00
-- url     : https://prove2.me/theorems/ba1e1ce8-06d9-524e-a858-987248e1d113
-- title:
--   Is Pushforward Blowup Seq: comp
-- statement:
--   The Is Pushforward Blowup Seq construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardComposition.lean#L22-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardComposition.lean#L22-L81

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardComposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq

theorem FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.comp {Y H X : Scheme.{u}} (σ : Y ⟶ H) [IsClosedImmersion σ]
    (ρ : H ⟶ X) [IsClosedImmersion ρ]
    {s : SequenceOfBlowups Y} {t : SequenceOfBlowups H} {u : SequenceOfBlowups X}
    (hNt : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hNu : ∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.IsNoetherian (u.schemeAt i))
    (hst : IsPushforwardBlowupSeq σ s t) (htu : IsPushforwardBlowupSeq ρ t u) :
    IsPushforwardBlowupSeq (σ ≫ ρ) s u := by sorry
