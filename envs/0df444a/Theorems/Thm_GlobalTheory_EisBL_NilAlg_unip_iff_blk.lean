-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_unip_iff_blk
-- name    : GlobalTheory.EisBL.NilAlg.unip_iff_blk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:11:14.357771+00:00
-- url     : https://prove2.me/theorems/939f516f-1cf0-4bf2-87e7-9b4f61102ee7
-- title:
--   Nil Alg: unip iff blk
-- statement:
--   The Nil Alg construction uses the unip iff blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L125-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L125-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.EisBL.NilAlg.unip_iff_blk (M : Matrix (n ⊕ n) (n ⊕ n) B) :
    ((M - 1) * Matrix.fromRows (1 : Matrix n n B) (1 : Matrix n n B) = 0 ∧
      Matrix.fromCols (1 : Matrix n n B) (-1 : Matrix n n B) * (M - 1) = 0) ↔
      ∃ X, M = blk X := by sorry
