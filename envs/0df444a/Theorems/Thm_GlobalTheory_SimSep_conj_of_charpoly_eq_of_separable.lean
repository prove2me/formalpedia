-- Prove2me | Theorems.Thm_GlobalTheory_SimSep_conj_of_charpoly_eq_of_separable
-- name    : GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:05.196489+00:00
-- url     : https://prove2.me/theorems/6029db92-687a-4b60-aff2-2805d94f74fa
-- title:
--   Sim Sep: conj of charpoly eq of separable
-- statement:
--   The Sim Sep construction uses the conj of charpoly eq of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyEqOfCharpolySeparable.lean#L50-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyEqOfCharpolySeparable.lean#L50-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.SimSep

theorem GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable : ∀ (R : Type) [Field R] (m : ℕ)
    (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable →
    ∃ P : GL (Fin m) R, N * P.val = P.val * U := by sorry
