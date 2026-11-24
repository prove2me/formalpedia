-- Prove2me | Theorems.Thm_GlobalTheory_MxDet_iterD_linF_pow
-- name    : GlobalTheory.MxDet.iterD_linF_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:30:11.791816+00:00
-- url     : https://prove2.me/theorems/57119780-6355-42b1-9855-efe252b0c8ba
-- title:
--   Mx Det: iter D lin F pow
-- statement:
--   The Mx Det construction uses the iter D lin F pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.MxDet

theorem GlobalTheory.MxDet.iterD_linF_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (linF x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * linF x ^ (N - m)
  := by sorry
