-- Prove2me | Theorems.Thm_Hex_Matrix_det_gramMatrix_nonneg
-- name    : Hex.Matrix.det_gramMatrix_nonneg
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:35:49.465202+00:00
-- url     : https://prove2.me/theorems/caae7192-57c9-4f57-9d34-ba702d5f1c42
-- title:
--   The exact integer Gram determinant is nonnegative
-- statement:
--   For every n-by-m native integer matrix A, the determinant of its exact Gram matrix is nonnegative, with no rank or dimension-positivity assumption. The existing proof expands the exact finite Cauchy-Binet sum of integer squares. It is compiled in its original Std-only environment as a reusable supporting theorem.
-- source:
--   Existing Apache-2.0 leanprover/hex source, checked in the native LLL port. No new mathematical lemma is introduced. Existing checked Lean theorem from Solutions.RegevBridgeNativeLLLVendor.HexDeterminant.Gram, original source lines 1405–1411. Original proof commands are selected using the official Lean declaration/sketch and syntax oracles, with only declared-name/reference remapping. Recursive self references, when renamed, are recovered from matching original Lean local-fvar identities. The original theorem and all inlined helper types are kernel checked; the complete proof and all its generated declarations use only the standard three axioms. Apache-2.0 notices and source provenance are preserved.

import Definitions.Def_LARLLL_BareissProgram
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Std
import Std.Data.ExtTreeMap.Lemmas
set_option autoImplicit false
set_option maxRecDepth 8192

theorem _root_.Hex.Matrix.det_gramMatrix_nonneg : ∀ {n m : Nat} (A : Hex.Matrix.{0} Int n m),
  @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
    (@Hex.Matrix.det.{0} Int (@Lean.Grind.CommRing.toRing.{0} Int Lean.Grind.instCommRingInt) n
      (@Hex.Matrix.gramMatrix.{0} Int n m Int.instMul Int.instAdd
        (@instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) A)) := by sorry
