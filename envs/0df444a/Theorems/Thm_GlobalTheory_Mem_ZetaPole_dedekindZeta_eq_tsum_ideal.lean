-- Prove2me | Theorems.Thm_GlobalTheory_Mem_ZetaPole_dedekindZeta_eq_tsum_ideal
-- name    : GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:55.344099+00:00
-- url     : https://prove2.me/theorems/58e0d339-8e6f-41de-907d-b72f0a70f5b1
-- title:
--   Zeta Pole: dedekind Zeta eq tsum ideal
-- statement:
--   The Zeta Pole construction uses the dedekind Zeta eq tsum ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L8-L28

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

theorem GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by sorry
