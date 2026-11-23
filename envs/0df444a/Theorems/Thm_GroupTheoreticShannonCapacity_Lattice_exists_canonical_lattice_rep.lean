-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_exists_canonical_lattice_rep
-- name    : GroupTheoreticShannonCapacity.Lattice.exists_canonical_lattice_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:28:21.105064+00:00
-- url     : https://prove2.me/theorems/a3599722-3203-45b9-8848-e9ca27eed1bb
-- title:
--   Lattice: exists canonical lattice rep
-- statement:
--   For any quotient element, there exists a canonical representative in the lattice
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L176-L236
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L176-L236

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

theorem GroupTheoreticShannonCapacity.Lattice.exists_canonical_lattice_rep (n : ℕ) [NeZero n] (p : ℕ) [hp : NeZero p]
    (A B : Matrix (Fin n) (Fin n) ℤ) (hAB : A * B = p • 1)
    (x : Fin n → ZMod p) (hx : x ∈ latticeQuotient n p A) :
    ∃ v : Fin n → ℤ,
      (fun i => (v i : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)) ∧
      (∀ i, (v i : ZMod p) = x i) ∧
      (∀ i, |v i| ≤ p / 2) ∧
      (∀ i, v i = canonicalRep p (x i)) := by sorry
