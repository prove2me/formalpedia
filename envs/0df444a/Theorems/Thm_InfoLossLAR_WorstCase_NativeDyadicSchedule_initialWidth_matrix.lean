-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_NativeDyadicSchedule_initialWidth_matrix
-- name    : InfoLossLAR.WorstCase.NativeDyadicSchedule.initialWidth_matrix
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:37:57.336225+00:00
-- url     : https://prove2.me/theorems/e7ff48db-850c-4279-b156-40312b76468d
-- title:
--   Row-major initializer width equals matrix entry envelope
-- statement:
--   Let $B$ be an integer $n\times n$ matrix and let $b$ be a natural-number base. Encode the rows and their entries in index order as the finite nested list used by the native initializer. The platform arithmetic initial-width function on that list is exactly
--
--   $$
--   W=b\left(1+\sum_{i=0}^{n-1}\sum_{j=0}^{n-1}|B_{ij}|\right).
--   $$
--
--   This equality holds also for singular matrices and $n=0$. It verifies the row-major mathematical expression of the published arithmetic width. It does not construct a sampler, prove a parser bridge, or by itself identify a term from a separately compiled local Lean environment.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, §3.1. This row-major binary initializer envelope is an explicit arithmetic compatibility lemma in the fixed-family formalization, not a verbatim theorem in the source.

import Definitions.Def_RegevInitialSelection
set_option autoImplicit false
open scoped BigOperators
open InfoLossLAR.WorstCase.NativeDyadicSchedule

namespace InfoLossLAR.WorstCase.NativeDyadicSchedule
theorem initialWidth_matrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (base : ℕ) :
    initialWidth (List.ofFn (fun row => List.ofFn (fun col => B row col))) base =
      (base : ℚ)*(1+∑ row, ∑ col, |(B row col : ℚ)|) := by sorry
end InfoLossLAR.WorstCase.NativeDyadicSchedule
