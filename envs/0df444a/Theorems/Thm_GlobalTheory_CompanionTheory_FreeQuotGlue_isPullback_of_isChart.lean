-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_isPullback_of_isChart
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:41:51.010803+00:00
-- url     : https://prove2.me/theorems/c8ea99eb-98c5-43ff-a025-fc2b0e611b7d
-- title:
--   Free Quot Glue: is Pullback of is Chart
-- statement:
--   The Free Quot Glue construction uses the is Pullback of is Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackOfGluedCharts.lean#L49-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackOfGluedCharts.lean#L49-L85

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type}
    (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hch : ∀ j, IsChart a b (V j) (q j))
    (hc : ∀ j, (V j).ι ≫ π = q j ≫ em j) (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j)
    (hcov : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) : IsPullback a b π π := by sorry
