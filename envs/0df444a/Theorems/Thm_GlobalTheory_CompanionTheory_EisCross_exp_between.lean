-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisCross_exp_between
-- name    : GlobalTheory.CompanionTheory.EisCross.exp_between
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:59.194386+00:00
-- url     : https://prove2.me/theorems/abe3ee06-e05f-4fb9-ad99-fd5f3dfacf07
-- title:
--   Eis Cross: exp between
-- statement:
--   The Eis Cross construction uses the exp between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoarseLipschitzExponentialEstimate.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoarseLipschitzExponentialEstimate.lean#L29-L39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisCross
open PositivityTheory.RgEis

theorem GlobalTheory.CompanionTheory.EisCross.exp_between (e₁ e₂ t s : ℝ) (h₁ : e₁ ≤ t) (h₂ : t ≤ e₂) :
    Real.exp (t * s) ≤ Real.exp (e₁ * s) + Real.exp (e₂ * s) := by sorry
