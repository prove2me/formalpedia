-- Prove2me | Theorems.Thm_HunterPDE_Shared_iteratedFDeriv_apply_coordinate_list
-- name    : HunterPDE.Shared.iteratedFDeriv_apply_coordinate_list
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:10:34.394188+00:00
-- url     : https://prove2.me/theorems/42a27189-4e9b-4016-993a-fbc3c9e0843b
-- title:
--   Iterated Frechet derivatives evaluated on coordinate lists
-- statement:
--   For a smooth real-valued function u on an open set s in Euclidean n-space, evaluating the kth iterated Frechet derivative at x∈s on the standard basis vectors indexed by a list l of length k gives the iterated coordinate derivative along l at x. The derivative order follows the published definition, with the first list entry applied last in the nested differentiation. The empty-list case is included.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, Section 1.8, printed p.10, and Theorem 1.27, printed pp.10–11, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Supporting coordinate-calculus interface extracted from the definitions and the coordinate expansion of the Taylor differential; this is not a verbatim numbered source theorem.

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem HunterPDE.Shared.iteratedFDeriv_apply_coordinate_list {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (l : List (Fin n)) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) :
    iteratedFDeriv ℝ l.length u x (fun j => EuclideanSpace.single (l.get j) 1) =
      iteratedPartial u l x := by sorry
