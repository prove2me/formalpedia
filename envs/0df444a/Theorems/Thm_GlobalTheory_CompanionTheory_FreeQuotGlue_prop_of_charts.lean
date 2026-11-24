-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_prop_of_charts
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.prop_of_charts
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:41:24.274688+00:00
-- url     : https://prove2.me/theorems/43569197-6bce-48cf-a790-8d658a4bb0c5
-- title:
--   Free Quot Glue: prop of charts
-- statement:
--   The Free Quot Glue construction uses the prop of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/QuotientOfAffineChartCover.lean#L65-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/QuotientOfAffineChartCover.lean#L65-L83

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimageStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCoverStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedChartsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_QuotientOfAffineChartCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.prop_of_charts (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {X Y' : Scheme.{0}} (π : X ⟶ Y') {J : Type} (V : J → X.Opens)
    (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hcomm : ∀ j, (V j).ι ≫ π = q j ≫ em j)
    (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j) (hsurj : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y)
    (hq : ∀ j, Q (q j)) : Q π := by sorry
