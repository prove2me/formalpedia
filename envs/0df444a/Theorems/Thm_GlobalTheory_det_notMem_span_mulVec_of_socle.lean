-- Prove2me | Theorems.Thm_GlobalTheory_det_notMem_span_mulVec_of_socle
-- name    : GlobalTheory.det_notMem_span_mulVec_of_socle
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:56.100154+00:00
-- url     : https://prove2.me/theorems/2c72e9bc-73a9-4594-8f81-989fe5bf52ff
-- title:
--   Global Theory: det not Mem span mul Vec of socle
-- statement:
--   The Global Theory construction uses the det not Mem span mul Vec of socle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetNotMemSpanMulVecOfSocle.lean#L9-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetNotMemSpanMulVecOfSocle.lean#L9-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetUpdateRowAlternatingMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetNotMemSpanMulVecOfSocle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.det_notMem_span_mulVec_of_socle {T : Type} [CommRing T] {g N : ℕ} (x : Fin g → T)
    (hsyz : ∀ r : Fin g → T, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) T,
      s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x)
    (hsoc : ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)))
    (a : Matrix (Fin g) (Fin g) T)
    (h : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range (a.mulVec x))) :
    a.det ∉ Ideal.span (Set.range (a.mulVec x)) := by sorry
