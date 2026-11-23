-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_matrixToIndependentSet
-- name    : GroupTheoreticShannonCapacity.Lattice.matrixToIndependentSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:25:41.411735+00:00
-- url     : https://prove2.me/theorems/7507c8ed-54e6-43be-87c6-72979f40eff8
-- title:
--   Lattice: matrix To Independent Set
-- statement:
--   Main lattice lemma (Lemma 2.1): If AB = pI and λ_∞(L(A)) ≥ q, then there exists
--       a subgroup independent set in E_{p/q}^⊠n of size at least |det(B)|.
--
--       Proof outline from paper:
--       1. Define S = {v mod p : v ∈ L(A)} ⊆ (ℤ/pℤ)^n
--       2. S is a subgroup (lattice closed under +)
--       3. pℤ^n ⊆ L(A) (from AB = pI)
--       4. S is independent: For nonzero x ∈ S, take representative v with |vᵢ| ≤ p/2.
--          Since x ≠ 0, v ≠ 0 mod pℤ^n, so v ∉ pℤ^n, meaning ‖v‖_∞ ≥ q.
--          This implies dist(xᵢ, 0) ≥ q for some i.
--       5. |S| = |L(A)/pℤ^n| = p^n/|det(A)| = |det(B)|
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L524-L648
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L524-L648

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

theorem GroupTheoreticShannonCapacity.Lattice.matrixToIndependentSet
    (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (p q : ℕ) [hp : NeZero p] (hq : 0 < q)
    (hAB : A * B = p • 1)
    (hMinDist : minDistance n (latticeOfMatrix n (A.map (↑· : ℤ → ℝ))) ≥ q) :
    ∃ S : AddSubgroup (Fin n → ZMod p),
      (strongPower (fractionGraph p q) n).IsIndepSet (S : Set (Fin n → ZMod p)) ∧
      Nat.card S ≥ Int.natAbs B.det := by sorry
