-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_eval_map_int
-- name    : GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.eval_map_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:33.11345+00:00
-- url     : https://prove2.me/theorems/e96c8fbe-096e-5920-92d4-9c5d51f80c80
-- title:
--   Segre Form: eval map int
-- statement:
--   The Segre Form construction uses the eval map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L77-L79

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

theorem GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.eval_map_int {σ : Type} (w : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by sorry
