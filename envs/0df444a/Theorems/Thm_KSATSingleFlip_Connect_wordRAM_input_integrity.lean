-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_wordRAM_input_integrity
-- name    : KSATSingleFlip.Connect.wordRAM_input_integrity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:55:14.85618+00:00
-- url     : https://prove2.me/theorems/93c7eb91-f022-465f-a04a-00dcdf374836
-- title:
--   Word-RAM sparse-input and width integrity
-- statement:
--   In the candidate fixed-width word-RAM model, serialization of a sparse formula and a start assignment with a requested variable has exactly $4+2km+n$ words; serialization with a target assignment has exactly $3+2km+2n$ words. Every serialized word fits in the declared word width. A halted machine state remains unchanged for any number of additional steps. This verifies representation and clock conventions only; it does not establish a k-SAT algorithm or a running-time bound.
-- source:
--   Formalization of the compact path representation of Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed p. 32 (PDF p. 34), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf. The cited paper does not fix this particular RAM instruction set.

import Definitions.Def_KSATSingleFlip_Connect_WordRAM

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Sparse RAM inputs fit their declared word width and have exact lengths. -/
theorem wordRAM_input_integrity (n k m T : ℕ) :
    (∀ (F : SparseFormula n k m) (x : Fin n → Bool) (v : Fin n),
      (sparseFlipInput F x v).length = sparseFlipInputWords n k m ∧
      ∀ a ∈ sparseFlipInput F x v, a < 2 ^ wordRAMWidth n k m T) ∧
    (∀ (F : SparseFormula n k m) (x y : Fin n → Bool),
      (sparseRouteInput F x y).length = sparseRouteInputWords n k m ∧
      ∀ a ∈ sparseRouteInput F x y, a < 2 ^ wordRAMRouteWidth n k m T) ∧
    (∀ (program : WordRAMProgram) (w : ℕ) (s : WordRAMState), s.halted = true →
      wordRAMRun program w T s = s) := by
  sorry

end KSATSingleFlip.Connect
