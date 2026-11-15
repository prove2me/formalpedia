-- Prove2me | Theorems.Thm_Hex_Matrix_bareissWith_eq_bareissDataWith_det
-- name    : Hex.Matrix.bareissWith_eq_bareissDataWith_det
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:37:43.540319+00:00
-- url     : https://prove2.me/theorems/e8ff23c3-362d-42ff-8048-80bf640f781f
-- title:
--   The executable Bareiss determinant equals the packaged elimination determinant
-- statement:
--   For every coefficient type with the stated arithmetic operations, every quotient function, dimension, and native square matrix M, bareissWith quot M equals the determinant encoded by bareissDataWith quot M. This is the exact original bridge between the executable array algorithm and its packaged matrix elimination data; no rank, nonsingularity, or quotient-correctness hypothesis is added.
-- source:
--   Existing Apache-2.0 leanprover/hex Bareiss implementation theorem. Existing checked Lean theorem from Solutions.RegevBridgeNativeLLLVendor.HexBareiss.Bareiss, original source lines 1495–1518. Original proof commands are selected using the official Lean declaration/sketch and syntax oracles, with only declared-name/reference remapping. Recursive self references, when renamed, are recovered from matching original Lean local-fvar identities. The original theorem and all inlined helper types are kernel checked; the complete proof and all its generated declarations use only the standard three axioms. Apache-2.0 notices and source provenance are preserved.

import Definitions.Def_LARLLL_BareissProgram
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Std
import Std.Data.ExtTreeMap.Lemmas
set_option autoImplicit false
set_option maxRecDepth 8192

theorem _root_.Hex.Matrix.bareissWith_eq_bareissDataWith_det.{u} : ∀ {R : Type u} {n : Nat} [inst : Zero.{u} R] [inst_1 : One.{u} R] [inst_2 : Neg.{u} R] [inst_3 : Sub.{u} R]
  [inst_4 : Mul.{u} R] [inst_5 : DecidableEq.{u + 1} R] {quot : R → R → R} (M : Hex.Matrix.{u} R n n),
  @Eq.{u + 1} R (@Hex.Matrix.bareissWith.{u} R n inst inst_1 inst_2 inst_3 inst_4 inst_5 quot M)
    (@Hex.Matrix.BareissData.det.{u} R n inst inst_1 inst_2 inst_4
      (@Hex.Matrix.bareissDataWith.{u} R n inst inst_1 inst_3 inst_4 inst_5 quot M)) := by sorry
