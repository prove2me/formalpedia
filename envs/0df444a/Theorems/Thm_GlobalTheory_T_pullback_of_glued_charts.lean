-- Prove2me | Theorems.Thm_GlobalTheory_T_pullback_of_glued_charts
-- name    : GlobalTheory.T.pullback_of_glued_charts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:55:07.177385+00:00
-- url     : https://prove2.me/theorems/f06902e9-1ca5-4666-bd9b-af2120aceb80
-- title:
--   T: pullback of glued charts
-- statement:
--   The T construction uses the pullback of glued charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackOfGluedChartsStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/PullbackOfGluedChartsStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedCharts
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedChartsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pullback_of_glued_charts : ∀ {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type} (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y') [∀ j, IsOpenImmersion (em j)], (∀ j, IsChart a b (V j) (q j)) → (∀ j, (V j).ι ≫ π = q j ≫ em j) → (∀ j, π ⁻¹ᵁ (em j).opensRange = V j) → (∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) → IsPullback a b π π := by sorry
