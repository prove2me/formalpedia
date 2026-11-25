-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_smooth_away_mul
-- name    : GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.smooth_away_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:44.826008+00:00
-- url     : https://prove2.me/theorems/5f40b9a0-aaba-4539-aaaf-47ba2f7c008b
-- title:
--   Segre Form: smooth away mul
-- statement:
--   The Segre Form construction uses the smooth away mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L63-L75

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.smooth_away_mul {B : Type} [CommRing B] [Algebra ℚ B] (s u : B) (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away (s * u)) := by sorry
