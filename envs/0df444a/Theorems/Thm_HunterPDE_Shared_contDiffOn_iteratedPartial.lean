-- Prove2me | Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
-- name    : HunterPDE.Shared.contDiffOn_iteratedPartial
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:10:47.320594+00:00
-- url     : https://prove2.me/theorems/85278c4b-3412-4371-907d-35571c6e1b9c
-- title:
--   Iterated coordinate derivatives remain smooth on an open set
-- statement:
--   If a real-valued function on Euclidean n-space is smooth on an open set s, then every iterated coordinate derivative indexed by a finite list is smooth on s. The empty list gives the original function. The coordinate derivatives are defined using the Frechet derivative and the standard basis, so the assertion applies to the published Hunter partial-derivative definitions.
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

theorem HunterPDE.Shared.contDiffOn_iteratedPartial {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (l : List (Fin n)) : ContDiffOn ℝ ∞ (iteratedPartial u l) s := by sorry
