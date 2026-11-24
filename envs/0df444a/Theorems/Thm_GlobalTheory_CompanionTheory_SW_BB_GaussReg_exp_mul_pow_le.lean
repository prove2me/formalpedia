-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_exp_mul_pow_le
-- name    : GlobalTheory.CompanionTheory.SW.BB.GaussReg.exp_mul_pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:25.1618+00:00
-- url     : https://prove2.me/theorems/3382bbe2-3706-46a0-a610-4377d79c6469
-- title:
--   Gauss Reg: exp mul pow le
-- statement:
--   The Gauss Reg construction uses the exp mul pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L78-L94

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianContinuousRapidDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.GaussReg

theorem GlobalTheory.CompanionTheory.SW.BB.GaussReg.exp_mul_pow_le {a : ℝ} (ha : 0 < a) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ} (hq : a * s ^ 2 ≤ q) :
    Real.exp (-q) * (1 + s) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (4 * a)) := by sorry
