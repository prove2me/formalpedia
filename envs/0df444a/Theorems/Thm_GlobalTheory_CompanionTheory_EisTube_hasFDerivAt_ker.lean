-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_hasFDerivAt_ker
-- name    : GlobalTheory.CompanionTheory.EisTube.hasFDerivAt_ker
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:16.644179+00:00
-- url     : https://prove2.me/theorems/c83d1309-89da-49b1-8d4f-265257ad59f6
-- title:
--   Eis Tube: has FDeriv At ker
-- statement:
--   The Eis Tube construction uses the has FDeriv At ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L136-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L136-L145

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

theorem GlobalTheory.CompanionTheory.EisTube.hasFDerivAt_ker {ι : Type} [Fintype ι] (w : ℂ) (t : ι → ℝ) (z : ι → ℂ) :
    HasFDerivAt (fun z : ι → ℂ => w * ker z t) ((w * ker z t) • lin t) z := by sorry
