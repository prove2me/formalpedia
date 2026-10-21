-- Prove2me | Theorems.Thm_MeasureTheory_Lp_infiniteDimensional_of_isOpen_euclidean
-- name    : MeasureTheory.Lp.infiniteDimensional_of_isOpen_euclidean
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T21:45:32.536012+00:00
-- url     : https://prove2.me/theorems/4297e5d9-bf6f-475e-ae87-7841022fd035
-- title:
--   L² of a nonempty Euclidean open set is infinite-dimensional
-- statement:
--   For n ≥ 1 and any nonempty open subset Ω of Euclidean n-space, the real Hilbert space L²(Ω), with restricted Lebesgue measure, is infinite-dimensional. Boundedness of Ω is unnecessary. One proof chooses countably many disjoint balls with positive finite measure inside a ball contained in Ω; their indicator functions are nonzero mutually orthogonal L² vectors. This is the dimension fact needed to index the eigenbasis in Hunter’s Theorem 4.25 by the natural numbers.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, sections 4.8–4.10, pp. 105–109, especially Theorem 4.25. https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

theorem MeasureTheory.Lp.infiniteDimensional_of_isOpen_euclidean
    {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hn : 1 ≤ n) (hne : Ω.Nonempty) :
    ¬ FiniteDimensional ℝ (Lp ℝ 2 (volume.restrict Ω)) := by sorry
