-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_norm_lin_le
-- name    : GlobalTheory.CompanionTheory.EisTube.norm_lin_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:05.369949+00:00
-- url     : https://prove2.me/theorems/40874101-49e9-4614-b133-1eb08ff9bd9f
-- title:
--   Eis Tube: norm lin le
-- statement:
--   The Eis Tube construction uses the norm lin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L121-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L121-L134

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

theorem GlobalTheory.CompanionTheory.EisTube.norm_lin_le {ι : Type} [Fintype ι] (t : ι → ℝ) :
    ‖lin t‖ ≤ 2 * Real.pi * ∑ i, |t i| := by sorry
