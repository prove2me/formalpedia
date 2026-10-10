-- Prove2me | Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
-- name    : HunterPDE.Shared.iteratedPartial_eq_of_perm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:17:15.656989+00:00
-- url     : https://prove2.me/theorems/ed246f1e-00a4-4352-87f1-bc5717df8c8c
-- title:
--   Mixed coordinate derivatives are invariant under list permutations
-- statement:
--   Let u be a smooth real-valued function on an open set s in Euclidean n-space. If two finite lists of coordinate indices are permutations of one another, their iterated coordinate derivatives agree at every point of s. The statement concerns derivatives along the entire lists, including repeated indices and the empty list. Smoothness ensures symmetry of second derivatives; adjacent swaps generate all list permutations.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, Section 1.8, printed p.10, and Theorem 1.27, printed pp.10–11, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Supporting coordinate-calculus interface extracted from the definitions and the coordinate expansion of the Taylor differential; this is not a verbatim numbered source theorem. Symmetry follows from Mathlib.Analysis.Calculus.FDeriv.Symmetric, ContDiffAt.isSymmSndFDerivAt.

import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem HunterPDE.Shared.iteratedPartial_eq_of_perm {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    {l t : List (Fin n)} (hp : l.Perm t) : Set.EqOn (iteratedPartial u l) (iteratedPartial u t) s := by sorry
