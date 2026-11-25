-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_isChart_id
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_id
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:46.070797+00:00
-- url     : https://prove2.me/theorems/fe1b3c7e-0e67-4a0f-a4dc-cc78cb63e908
-- title:
--   Free Quot Glue: is Chart id
-- statement:
--   The Free Quot Glue construction uses the is Chart id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean#L27-L31

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

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_id (X : Scheme.{0}) : IsChart (𝟙 X) (𝟙 X) ⊤ (⊤ : X.Opens).ι := by sorry
