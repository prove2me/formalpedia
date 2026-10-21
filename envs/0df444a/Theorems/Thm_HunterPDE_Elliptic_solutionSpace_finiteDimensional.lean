-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_solutionSpace_finiteDimensional
-- name    : HunterPDE.Elliptic.solutionSpace_finiteDimensional
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T21:50:17.371981+00:00
-- url     : https://prove2.me/theorems/f237b258-5e66-4f33-bbc6-f91626c7a977
-- title:
--   Finite-dimensional weak eigenspaces of an elliptic Dirichlet problem
-- statement:
--   For a bounded open Ω and any admissible uniformly elliptic operator P, the space of weak solutions of Lu−λu=0 in H¹₀(Ω) is finite-dimensional for every real λ. Symmetry and a sign condition on λ are unnecessary. This follows from either branch of Hunter’s Fredholm alternative, Theorem 4.24: in the unique branch the solution span is zero, and in the other branch finite-dimensionality is explicit.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, sections 4.8–4.10, pp. 105–109, especially Theorem 4.25. https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf

import Theorems.Thm_HunterPDE_Elliptic_fredholm_alternative

open MeasureTheory HunterPDE.Elliptic

theorem HunterPDE.Elliptic.solutionSpace_finiteDimensional {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (P : Coeffs n) (hP : P.Admissible Ω)
    (hell : P.UniformlyElliptic Ω) (lam : ℝ) :
    FiniteDimensional ℝ (solutionSpace (Ω := Ω) (form P) (-lam)) := by sorry
