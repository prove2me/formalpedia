-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_latticeOfMatrix_add_pZ
-- name    : GroupTheoreticShannonCapacity.Lattice.latticeOfMatrix_add_pZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:14.76694+00:00
-- url     : https://prove2.me/theorems/7d46f199-10df-4030-b153-d3c6a32ed355
-- title:
--   Lattice: lattice Of Matrix add p Z
-- statement:
--   Uniqueness of canonical representative: if w ≡ z (mod p) and |w| ≤ p/2, then
--       w = canonicalRep p z, with a caveat for the boundary case w = -p/2
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L154-L173
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L154-L173

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

theorem GroupTheoreticShannonCapacity.Lattice.latticeOfMatrix_add_pZ (n : ℕ) [NeZero n] (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ)
    (hAB : A * B = p • 1)
    (v : Fin n → ℤ) (hv : (fun i => (v i : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)))
    (k : Fin n → ℤ) :
    (fun i => ((v i + p * k i) : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)) := by sorry
