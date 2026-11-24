-- Prove2me | Theorems.Thm_GlobalTheory_wittSolve_unique
-- name    : GlobalTheory.wittSolve_unique
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:20.244866+00:00
-- url     : https://prove2.me/theorems/7116edc7-035e-4dae-82d5-6c876801b13c
-- title:
--   Global Theory: witt Solve unique
-- statement:
--   The Global Theory construction uses the witt Solve unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L196-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L196-L208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.wittSolve_unique : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)),
    (∀ c : ι → R, ∃! x : ι → R,
      x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) →
    ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R,
      v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by sorry
