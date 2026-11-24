-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_continuous_lin
-- name    : GlobalTheory.CompanionTheory.EisTube.continuous_lin
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:27.433022+00:00
-- url     : https://prove2.me/theorems/9ef3dcfc-fffe-452f-83ae-45ac939a14cc
-- title:
--   Eis Tube: continuous lin
-- statement:
--   The Eis Tube construction uses the continuous lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L117-L119

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

theorem GlobalTheory.CompanionTheory.EisTube.continuous_lin {ι : Type} [Fintype ι] : Continuous (lin (ι := ι)) := by sorry
