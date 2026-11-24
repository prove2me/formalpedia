-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_ChartRestrict_opensRange_homOfLE_eq
-- name    : GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict.opensRange_homOfLE_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:41:07.246376+00:00
-- url     : https://prove2.me/theorems/06b9ffea-7b15-41aa-aa0c-e53e8b0bb219
-- title:
--   Chart Restrict: opens Range hom Of LE eq
-- statement:
--   The Chart Restrict construction uses the opens Range hom Of LE eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ChartRestrictPreimageOpen.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/ChartRestrictPreimageOpen.lean#L14-L22

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpen
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict

theorem GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict.opensRange_homOfLE_eq {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) :
    (X.homOfLE h).opensRange = V.ι ⁻¹ᵁ U := by sorry
