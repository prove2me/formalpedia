-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_smooth_slab_poincare
-- name    : HunterPDE.Elliptic.smooth_slab_poincare
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T21:12:09.364244+00:00
-- url     : https://prove2.me/theorems/db110764-0e2f-47a5-93f0-15ffb26f4870
-- title:
--   Smooth Poincaré estimate on a slab with explicit width constant
-- statement:
--   Let $\Omega$ be an open subset of $\mathbb R^n$ contained in a slab $a<x\cdot e<b$, where $\|e\|=1$. Every smooth compactly supported real function $\varphi$ whose closed support lies in $\Omega$ satisfies
--
--   $$\int_\Omega \varphi^2\,dx \le (b-a)^2\int_\Omega \|\nabla\varphi\|^2\,dx.$$
--
--   The constant is independent of the function, and the domain need not be bounded in directions orthogonal to the slab normal. This is the smooth-function part of Hunter's Theorem 4.9: the fundamental theorem of calculus along normal lines, Cauchy–Schwarz, and Fubini give the estimate. It is independent of the Sobolev completion and is intended to extend to that completion by continuity. When the domain is empty both integrals vanish; otherwise its containment implies $a<b$.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 98, Theorem 4.9, smooth-function estimate in the proof. https://www.math.ucdavis.edu/~hunter/pdes/ch4.pdf

import Definitions.Def_HunterPDE_Elliptic_H10

open MeasureTheory
open scoped ContDiff

theorem HunterPDE.Elliptic.smooth_slab_poincare {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (a b : ℝ)
    (hab : ∀ x ∈ Ω, a < inner ℝ x e ∧ inner ℝ x e < b)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x in Ω, φ x ^ 2 ≤ (b-a)^2 * ∫ x in Ω, ‖gradient φ x‖ ^ 2 := by sorry
