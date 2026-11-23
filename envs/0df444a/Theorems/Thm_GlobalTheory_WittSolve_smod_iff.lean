-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_smod_iff
-- name    : GlobalTheory.WittSolve.smod_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:37.327397+00:00
-- url     : https://prove2.me/theorems/66bb56a9-93ec-47ce-b5aa-a62c678312be
-- title:
--   Witt Solve: smod iff
-- statement:
--   The Witt Solve construction uses the smod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L53-L57

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
open GlobalTheory GlobalTheory.WittSolve
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]

theorem GlobalTheory.WittSolve.smod_iff (x y : WittVector p R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {(p : WittVector p R)}) ^ n •
      (⊤ : Submodule (WittVector p R) (WittVector p R))] ↔ (p : WittVector p R) ^ n ∣ x - y := by sorry
