-- Prove2me | Theorems.Thm_HunterPDE_Shared_iteratedFDeriv_apply_coordinates_eq_multiDeriv
-- name    : HunterPDE.Shared.iteratedFDeriv_apply_coordinates_eq_multiDeriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:25:10.027986+00:00
-- url     : https://prove2.me/theorems/8c59796f-ec75-4e05-8b8a-647f2ee86b9b
-- title:
--   Coordinate evaluations of Frechet derivatives equal multi-index derivatives
-- statement:
--   Let u be a smooth real-valued function on an open set s in Euclidean n-space, and let x∈s. For any assignment a of k coordinate directions, let α_i count how many of those directions equal i. Evaluating the kth Frechet derivative on the standard basis vectors prescribed by a equals the multi-index derivative ∂^αu(x), with the fixed sorted coordinate order of the published Hunter definition. Repeated directions and k=0 are included. This identifies a differential tensor with its multi-index coefficients.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, Section 1.8, printed p.10, and Theorem 1.27, printed pp.10–11, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Supporting coordinate-calculus interface extracted from the definitions and the coordinate expansion of the Taylor differential; this is not a verbatim numbered source theorem.

import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
import Theorems.Thm_HunterPDE_Shared_iteratedFDeriv_apply_coordinate_list
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem HunterPDE.Shared.iteratedFDeriv_apply_coordinates_eq_multiDeriv {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) (a : Fin k → Fin n) :
    iteratedFDeriv ℝ k u x (fun j => EuclideanSpace.single (a j) 1) =
      multiDeriv u (fun i => (List.ofFn a).count i) x := by sorry
