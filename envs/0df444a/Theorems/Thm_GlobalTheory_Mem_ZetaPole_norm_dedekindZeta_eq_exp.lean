-- Prove2me | Theorems.Thm_GlobalTheory_Mem_ZetaPole_norm_dedekindZeta_eq_exp
-- name    : GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:47.228438+00:00
-- url     : https://prove2.me/theorems/ace52d04-f7b7-4737-be3a-6d26977c0cc1
-- title:
--   Zeta Pole: norm dedekind Zeta eq exp
-- statement:
--   The Zeta Pole construction uses the norm dedekind Zeta eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L70-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L70-L89

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

theorem GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    ‖dedekindZeta K s‖ =
      Real.exp (∑' v : HeightOneSpectrum (𝓞 K), logFactor (Ideal.absNorm v.asIdeal) s) := by sorry
