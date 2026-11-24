-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_re_le_of_dist
-- name    : GlobalTheory.CompanionTheory.EisTube.re_le_of_dist
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:04.818308+00:00
-- url     : https://prove2.me/theorems/0cfcdea0-18f3-4c5b-b137-771afc10f9dd
-- title:
--   Eis Tube: re le of dist
-- statement:
--   The Eis Tube construction uses the re le of dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L97-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L97-L108

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

theorem GlobalTheory.CompanionTheory.EisTube.re_le_of_dist {ι : Type} [Fintype ι] {z z₀ : ι → ℂ} (hz : dist z z₀ < 1) (i : ι) :
    |(z i).re| ≤ (∑ j, |(z₀ j).re|) + 1 := by sorry
