-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_isChart_pullback
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_pullback
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:00.162918+00:00
-- url     : https://prove2.me/theorems/a76ef6f0-1a62-4585-8425-8e0bf3306c3e
-- title:
--   Free Quot Glue: is Chart pullback
-- statement:
--   The Free Quot Glue construction uses the is Chart pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L33-L49

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
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
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_pullback {X Y : Scheme.{0}} (q : X ⟶ Y) [IsFinite q] [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    IsChart (pullback.fst q q) (pullback.snd q q) ⊤ ((⊤ : X.Opens).ι ≫ q) := by sorry
