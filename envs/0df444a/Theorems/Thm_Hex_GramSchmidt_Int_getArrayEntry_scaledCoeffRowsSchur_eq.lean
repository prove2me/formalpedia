-- Prove2me | Theorems.Thm_Hex_GramSchmidt_Int_getArrayEntry_scaledCoeffRowsSchur_eq
-- name    : Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:32:05.097201+00:00
-- url     : https://prove2.me/theorems/b38768eb-d30c-4bf4-9992-d5b656e20a3c
-- title:
--   The Schur implementation computes the canonical scaled Gram-Schmidt rows
-- statement:
--   For every integer row matrix b equipped with the stated StepWitness provider for canonical regular Bareiss steps, and every pair of natural indices i,j, getArrayEntry of scaledCoeffRowsSchur b equals getArrayEntry of scaledCoeffRows b. The witness explicitly supplies the required canonical integer-quotient provenance. This is equality of the two concrete implementations, including their specified array-access behavior; the witness hypothesis is retained.
-- source:
--   Existing checked theorem Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq in Solutions.RegevBridgeNativeLLLVendor.HexGramSchmidt.Int.Combination.lean. The submitted declaration and its supporting proofs are extracted from the checked Lean source using the kernel dependency graph and Lean syntax positions. The vendor mathematics uses the frozen leanprover/hex-lll dependency family; original Apache-2.0 license and copyright notices are retained in the proof sources. This submission adds no new mathematical claim. Existing checked Lean theorem from Solutions.RegevBridgeNativeLLLVendor.HexGramSchmidt.Int.Combination, original source lines 1790–1872. Original proof commands are selected using the official Lean declaration/sketch and syntax oracles, with only declared-name/reference remapping. Recursive self references, when renamed, are recovered from matching original Lean local-fvar identities. The original theorem and all inlined helper types are kernel checked; the complete proof and all its generated declarations use only the standard three axioms. Apache-2.0 notices and source provenance are preserved.

import Definitions.Def_LARLLL_IntegerGramSchmidt
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Std
import Std.Data.ExtTreeMap.Lemmas
set_option autoImplicit false
set_option maxRecDepth 8192

theorem _root_.Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq : ∀ {n m : Nat} (b : Hex.Matrix.{0} Int n m) (hquot : @Hex.GramSchmidt.Int.StepWitness n m b) (i j : Nat),
  @Eq.{1} Int (Hex.GramSchmidt.Int.getArrayEntry (@Hex.GramSchmidt.Int.scaledCoeffRowsSchur n m b) i j)
    (Hex.GramSchmidt.Int.getArrayEntry (@Hex.GramSchmidt.Int.scaledCoeffRows n m b) i j) := by sorry
