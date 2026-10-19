-- Prove2me | Theorems.Thm_HunterPDE_Shared_uniform_normalCutoff_multiDeriv_bound
-- name    : HunterPDE.Shared.uniform_normalCutoff_multiDeriv_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T15:27:25.617506+00:00
-- url     : https://prove2.me/theorems/22a40dd5-dc7a-4900-8387-9efb373eb4de
-- title:
--   Uniform multi-derivative bound for shrinking normal cutoffs
-- statement:
--   Fix a coordinate $i$ and a multi-index $\alpha$. Let $\psi$ be a smooth compactly supported real function on Euclidean space, with every pure normal derivative of order less than $\alpha_i$ vanishing on the coordinate hyperplane. Let $q$ be any smooth real cutoff equal to zero on $(-\infty,1]$ and one on $[2,\infty)$. There is a nonnegative constant $C$, independent of the real scale $a\ge1$ and of $x$, such that
--   $$|\partial^\alpha(q(a x_i)\psi(x))|\le C.$$
--   No bound on the cutoff in the transition interval is assumed: smoothness supplies all required bounds on that compact interval. The assertion includes zero normal order, when the boundary hypothesis is empty.
--
--   The intended proof expands by Leibniz, preserves vanishing normal jets under tangential differentiation, and uses one-dimensional Taylor bounds to cancel the scale factors on the shrinking transition strip. This quantitative calculus estimate is an Open proof obligation, separate from support geometry and convergence of an approximating sequence.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A (March 19, 2024), Proposition 11.13, proof Step 2, printed p.158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Auxiliary Taylor-Leibniz estimate for a boundary-test cutoff argument supporting the distributional reflection construction; this estimate is an additional analytic interface, not a verbatim result in the cited proposition. Taylor input: Mathlib.Analysis.Calculus.Taylor.taylor_mean_remainder_bound in pinned Mathlib 0df444a.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.uniform_normalCutoff_multiDeriv_bound
    {n : ℕ} (i : Fin n) (α : Fin n → ℕ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hb : ∀ r : ℕ, r < α i → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0)
    (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q)
    (hlo : ∀ s : ℝ, s ≤ 1 → q s = 0)
    (hhi : ∀ s : ℝ, 2 ≤ s → q s = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 1 ≤ a →
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖multiDeriv (fun y => q (a * y i) * ψ y) α x‖ ≤ C := by sorry
