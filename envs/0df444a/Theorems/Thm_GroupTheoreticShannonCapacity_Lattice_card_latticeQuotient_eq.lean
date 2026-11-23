-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_card_latticeQuotient_eq
-- name    : GroupTheoreticShannonCapacity.Lattice.card_latticeQuotient_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:46.859998+00:00
-- url     : https://prove2.me/theorems/41fe04e0-ff62-4d8d-8d00-25c93150887b
-- title:
--   Lattice: card lattice Quotient eq
-- statement:
--   The cardinality of latticeQuotient equals |det(B)|.
--
--       **Proof strategy using Mathlib lattice index theory:**
--
--       1. **Setup lattices as AddSubgroups of (Fin n → ℤ):**
--          - L(A) := { A * x : x ∈ ℤ^n } (image of A)
--          - pℤ^n := { p * x : x ∈ ℤ^n }
--
--       2. **Key index formula** (Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient):
--          - `AddSubgroup.index_eq_natAbs_det`: [ℤ^n : L(A)] = |det(A)|
--          - `AddSubgroup.relIndex_eq_natAbs_det`: [L₁ : L₂] = |det(basis change)|
--
--       3. **Compute |latticeQuotient|:**
--          - latticeQuotient ≅ L(A) / pℤ^n (since pℤ^n ⊆ L(A) from hAB)
--          - |latticeQuotient| = [L(A) : pℤ^n]
--          - By tower formula: [ℤ^n : pℤ^n] = [ℤ^n : L(A)] · [L(A) : pℤ^n]
--          - So [L(A) : pℤ^n] = p^n / |det(A)|
--
--       4. **Conclude using det(A) * det(B) = p^n:**
--          - From `det_mul_eq_pow_of_mul_eq_smul`: det(A) * det(B) = p^n
--          - So |det(B)| = p^n / |det(A)| = [L(A) : pℤ^n] = |latticeQuotient|
--
--       **Required infrastructure:**
--       - Basis for L(A): columns of A
--       - Basis for pℤ^n: p * standard basis
--       - Verify latticeQuotient ≅ L(A) / pℤ^n via first isomorphism theorem
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L478-L511
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L478-L511

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.Lattice.card_latticeQuotient_eq (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) [NeZero p]
    (hAB : A * B = p • 1) (hdetA : A.det ≠ 0) :
    Nat.card (latticeQuotient n p A) = B.det.natAbs := by sorry
