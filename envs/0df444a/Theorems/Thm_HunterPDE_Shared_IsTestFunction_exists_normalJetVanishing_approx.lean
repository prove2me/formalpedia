-- Prove2me | Theorems.Thm_HunterPDE_Shared_IsTestFunction_exists_normalJetVanishing_approx
-- name    : HunterPDE.Shared.IsTestFunction.exists_normalJetVanishing_approx
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T13:45:35.866073+00:00
-- url     : https://prove2.me/theorems/6ae25a08-4bff-423f-b6e5-9abc2d50b059
-- title:
--   Interior test approximation under vanishing normal boundary jets
-- statement:
--   Let H be any positive coordinate half-space and let ψ be a smooth compactly supported real function on Euclidean space. Fix a multi-index α and suppose every pure normal derivative of ψ of order strictly below α in the normal coordinate vanishes on the boundary hyperplane. There exist smooth compactly supported tests φ_j whose closed supports lie inside H, a common compact set K, and a nonnegative constant C such that both φ_j and their α-th derivatives are bounded in absolute value by C times the indicator of K. At every point of H these functions and their α-th derivatives converge respectively to ψ and its α-th derivative. Normal order zero requires no boundary vanishing. This is a purely smooth approximation statement, independent of weak derivatives or locally integrable data. A proposed construction multiplies ψ by a smooth cutoff of (j+1) times the normal coordinate; tangential differentiation preserves vanishing normal jets, and one-dimensional Taylor estimates bound all shrinking-strip Leibniz terms uniformly. The construction is an Open proof obligation.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A (March 19, 2024), Proposition 11.13, proof Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Independent analytic and calculus interfaces for the distributional justification; the weak-data boundary step is an additional cutoff argument, not attributed to the smooth calculation alone. This approximation lemma is an additional analytic interface for the weak-data argument, not a verbatim claim in Proposition 11.13.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Topology.Algebra.Order.Field
open MeasureTheory Filter HunterPDE.Shared
open scoped Topology
set_option autoImplicit false

theorem HunterPDE.Shared.IsTestFunction.exists_normalJetVanishing_approx
    {n : ℕ} (i : Fin n) (α : Fin n → ℕ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : IsTestFunction Set.univ ψ)
    (hb : ∀ r : ℕ, r < α i → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
          (∀ j, IsTestFunction {x | 0 < x i} (φ j)) ∧
          (∀ j x, ‖φ j x‖ ≤ K.indicator (fun _ => C) x ∧
            ‖multiDeriv (φ j) α x‖ ≤ K.indicator (fun _ => C) x) ∧
          (∀ x : EuclideanSpace ℝ (Fin n), 0 < x i →
            Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)) ∧
            Tendsto (fun j => multiDeriv (φ j) α x) atTop (𝓝 (multiDeriv ψ α x))) := by sorry
