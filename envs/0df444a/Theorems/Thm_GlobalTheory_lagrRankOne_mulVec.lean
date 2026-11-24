-- Prove2me | Theorems.Thm_GlobalTheory_lagrRankOne_mulVec
-- name    : GlobalTheory.lagrRankOne_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:25.245931+00:00
-- url     : https://prove2.me/theorems/00d5407a-23ab-4a03-b783-772458dd4262
-- title:
--   Global Theory: lagr Rank One mul Vec
-- statement:
--   The Global Theory construction uses the lagr Rank One mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleLagrangianTransverseField.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleLagrangianTransverseField.lean#L39-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.lagrRankOne_mulVec {k : Type} [Field k] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k) :
    lagrRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by sorry
