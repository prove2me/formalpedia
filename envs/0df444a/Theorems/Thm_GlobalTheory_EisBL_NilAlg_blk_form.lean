-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_blk_form
-- name    : GlobalTheory.EisBL.NilAlg.blk_form
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:43.100836+00:00
-- url     : https://prove2.me/theorems/6ffd379a-a793-4bce-a8ec-5b09ee3c2ac9
-- title:
--   Nil Alg: blk form
-- statement:
--   The Nil Alg construction uses the blk form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L29-L36

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

theorem GlobalTheory.EisBL.NilAlg.blk_form (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c =
      GlobalTheory.WeilM.dbl J + fromBlocks (phi c J X) (-phi c J X) (-phi c J X) (phi c J X) := by sorry
