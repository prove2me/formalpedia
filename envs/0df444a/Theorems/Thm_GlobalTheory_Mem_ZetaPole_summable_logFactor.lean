-- Prove2me | Theorems.Thm_GlobalTheory_Mem_ZetaPole_summable_logFactor
-- name    : GlobalTheory.Mem.ZetaPole.summable_logFactor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:46.479318+00:00
-- url     : https://prove2.me/theorems/76a1d4a3-377d-4921-ae0e-7949a6aaf4a8
-- title:
--   Zeta Pole: summable log Factor
-- statement:
--   The Zeta Pole construction uses the summable log Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L59-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.ZetaPole

theorem GlobalTheory.Mem.ZetaPole.summable_logFactor (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => logFactor (Ideal.absNorm v.asIdeal) s := by sorry
