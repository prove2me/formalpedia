-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_integrable_exp_neg_sum_abs
-- name    : GlobalTheory.CompanionTheory.EisTube.integrable_exp_neg_sum_abs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:36.747317+00:00
-- url     : https://prove2.me/theorems/bbe5244f-f60b-420d-9d04-efbd8702af6d
-- title:
--   Eis Tube: integrable exp neg sum abs
-- statement:
--   The Eis Tube construction uses the integrable exp neg sum abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L12-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.integrable_exp_neg_sum_abs {ι : Type} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ι → ℝ => Real.exp (-(c * ∑ i, |t i|))) := by sorry
