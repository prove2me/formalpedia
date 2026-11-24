-- Prove2me | Theorems.Thm_GlobalTheory_IdealSum_tsum_idealLattice
-- name    : GlobalTheory.IdealSum.tsum_idealLattice
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:04:49.132507+00:00
-- url     : https://prove2.me/theorems/7772b6e5-3df1-4a2f-9f7a-6dba53579fc4
-- title:
--   Ideal Sum: tsum ideal Lattice
-- statement:
--   The Ideal Sum construction uses the tsum ideal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealSumPeriodicDilate.lean#L75-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealSumPeriodicDilate.lean#L75-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptoticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.IdealSum

theorem GlobalTheory.IdealSum.tsum_idealLattice (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰)
    (F : mixedSpace K → ℂ) :
    ∑' l : idealLattice K (FractionalIdeal.mk0 K J), F l =
      ∑' β : ↥(J.1), F (mixedEmbedding K ((β : 𝓞 K) : K)) := by sorry
