-- Prove2me | Theorems.Thm_HunterPDE_Shared_hasWeakDeriv_partial_of_contDiffOn
-- name    : HunterPDE.Shared.hasWeakDeriv_partial_of_contDiffOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T16:21:41.772983+00:00
-- url     : https://prove2.me/theorems/c8f47880-4995-4e53-bc1f-22de5d086906
-- title:
--   Classical first partial derivatives are weak derivatives on an open set
-- statement:
--   Let Ω be an open subset of Euclidean space and let f be continuously differentiable on Ω. For every coordinate i, the classical partial derivative ∂ᵢf is a weak first derivative on Ω. Both functions are locally integrable there, and integration by parts holds against every smooth test function with compact support contained in Ω. No assumptions on f outside Ω, boundary regularity, or compact support of f are required.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definitions 3.1–3.2 and discussion on printed pp. 47–48: continuously differentiable functions have their classical derivatives as weak derivatives. The C¹ open-set case is proved by integration by parts against compactly supported tests.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.hasWeakDeriv_partial_of_contDiffOn {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ 1 f Ω) (i : Fin n) :
    HasWeakDeriv Ω (Pi.single i 1) f (partialDeriv f i) := by sorry
