-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_mul_exp_le
-- name    : GlobalTheory.CompanionTheory.EisTube.mul_exp_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:39.155898+00:00
-- url     : https://prove2.me/theorems/f6a15366-a281-44a4-8830-46bb58f59a80
-- title:
--   Eis Tube: mul exp le
-- statement:
--   The Eis Tube construction uses the mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L147-L156

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

theorem GlobalTheory.CompanionTheory.EisTube.mul_exp_le {S : ℝ} (hS : 0 ≤ S) :
    S * Real.exp (-(2 * Real.pi * S)) ≤ Real.exp (-S) := by sorry
