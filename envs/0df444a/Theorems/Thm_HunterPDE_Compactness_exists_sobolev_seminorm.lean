-- Prove2me | Theorems.Thm_HunterPDE_Compactness_exists_sobolev_seminorm
-- name    : HunterPDE.Compactness.exists_sobolev_seminorm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:03:29.832832+00:00
-- url     : https://prove2.me/theorems/0a092de4-09b6-496a-acb3-5780d04647f4
-- title:
--   The finite-p Sobolev space carries its canonical seminorm
-- statement:
--   For every open subset of Euclidean space and every finite exponent $1\le p<\infty$, the raw representatives in $W^{k,p}$ form a real vector subspace, and their Sobolev norm is the extended-real image of a finite real seminorm on that subspace. No quotient by almost-everywhere equality is taken. The seminorm may therefore vanish on nonzero raw functions. This assertion includes the triangle inequality, absolute homogeneity, finiteness, and closure under real linear combinations for the chosen weak-derivative representatives.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definition 3.23, printed pp.58–59. Seminorm formulation on raw representatives of the Sobolev norm; standard consequence of weak-derivative linearity, uniqueness and finite-sum Minkowski.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.Analysis.Seminorm
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.exists_sobolev_seminorm {n k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    ∃ W : Submodule ℝ (EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ f, f ∈ W ↔ MemW k p Ω f) ∧
      ∃ q : Seminorm ℝ W, ∀ f : W,
        ENNReal.ofReal (q f) = sobolevNorm k p Ω f := by sorry
