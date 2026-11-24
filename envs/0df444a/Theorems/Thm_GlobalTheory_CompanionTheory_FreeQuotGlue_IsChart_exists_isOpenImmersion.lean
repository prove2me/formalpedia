-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_exists_isOpenImmersion
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_isOpenImmersion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:41:22.219232+00:00
-- url     : https://prove2.me/theorems/67173fa2-d47d-4848-81e1-451627baa808
-- title:
--   Is Chart: exists is Open Immersion
-- statement:
--   The Is Chart construction uses the exists is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/QuotientOfAffineChartCover.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/QuotientOfAffineChartCover.lean#L31-L41

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

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_isOpenImmersion {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {V V' : X.Opens}
    {q : V.toScheme ⟶ Y} {q' : V'.toScheme ⟶ Y'} (h : IsChart a b V q) (h' : IsChart a b V' q')
    (hle : V' ≤ V) : ∃ k : Y' ⟶ Y, IsOpenImmersion k ∧ q' ≫ k = X.homOfLE hle ≫ q := by sorry
