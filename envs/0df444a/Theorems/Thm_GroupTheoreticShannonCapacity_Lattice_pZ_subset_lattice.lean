-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_pZ_subset_lattice
-- name    : GroupTheoreticShannonCapacity.Lattice.pZ_subset_lattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:05.243387+00:00
-- url     : https://prove2.me/theorems/91e698fe-c6ea-486d-b96f-d232d059692d
-- title:
--   Lattice: p Z subset lattice
-- statement:
--   For a lattice L(A) with AB = pI, the sublattice pℤ^n is contained in L(A).
--       Proof: p * v = (AB) * v = A * (B * v), so p * v ∈ L(A).
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L46-L68
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L46-L68

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

theorem GroupTheoreticShannonCapacity.Lattice.pZ_subset_lattice (n : ℕ) [NeZero n] (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ)
    (hAB : A * B = p • 1) :
    ∀ v : Fin n → ℤ, (fun i => (p * v i : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)) := by sorry
