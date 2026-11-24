-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExpSums_tendsto_one_add_pow_mul_pow
-- name    : GlobalTheory.CompanionTheory.ExpSums.tendsto_one_add_pow_mul_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:33.400514+00:00
-- url     : https://prove2.me/theorems/28bc4095-ada2-4a78-b889-f5aae182a741
-- title:
--   Exp Sums: tendsto one add pow mul pow
-- statement:
--   The Exp Sums construction uses the tendsto one add pow mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RegularizedExponentialSum.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RegularizedExponentialSum.lean#L10-L24

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VandermondeSeparation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExpSums

theorem GlobalTheory.CompanionTheory.ExpSums.tendsto_one_add_pow_mul_pow {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (N : ℕ) :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ N * t ^ n) atTop (𝓝 0) := by sorry
