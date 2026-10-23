-- Prove2me | Theorems.Thm_JHolomorphic_exists_memLp_sum_mul_apply_eq
-- name    : JHolomorphic.exists_memLp_sum_mul_apply_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:37:24.299376+00:00
-- url     : https://prove2.me/theorems/d1564552-824f-4bcd-9392-bf38e429d3b7
-- title:
--   A bounded operator field transposing a pointwise linear relation
-- statement:
--   Let $\rho>0$, $M\in\mathbb{R}$, and $g,w:\mathbb{C}\to\mathbb{C}^n$ continuous on the disc $D_\rho$ with $\|w(z)\|\le M\|g(z)\|$ for $z\in D_\rho$. For every $p\in(0,\infty]$ there is $A:\mathbb{C}\to\mathcal{L}_{\mathbb{R}}(\mathbb{C}^n,\mathbb{C}^n)$ with $A\in L^p(D_1)$ such that for all $|z|\le\rho/2$ and all $r\in\mathbb{C}^n$
--   $$\sum_{i} g_i(z)\,\big(A(z)r\big)_i=\sum_i w_i(z)\,r_i .$$
--
--   It converts a pointwise bound of $w$ by $g$ into a bounded (possibly discontinuous) linear coefficient field relating them through the bilinear pairing $\sum_i a_ib_i$; this is the kind of coefficient used in similarity principles for Cauchy–Riemann type equations.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, components are `v i`, $A$ has type `ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)` and $A\in L^p(D_1)$ is `MemLp A p (volume.restrict (ball 0 1))`.
-- source:
--   Standard; Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Let `g, w : ℂ → ℂⁿ` be continuous on `B(0,ρ)` with `‖w z‖ ≤ M ‖g z‖` there. Then there is a
real-linear operator field `A` in `L^p` on the unit disc with `∑ᵢ gᵢ(z) (A(z) r)ᵢ = ∑ᵢ wᵢ(z) rᵢ` for
all `r ∈ ℂⁿ` and `|z| ≤ ρ/2`. -/
theorem exists_memLp_sum_mul_apply_eq (n : ℕ) (ρ M : ℝ) (hρ : 0 < ρ) (g w : ℂ → EuclideanSpace ℂ (Fin n))
    (hg : ContinuousOn g (ball 0 ρ)) (hw : ContinuousOn w (ball 0 ρ))
    (hM : ∀ z ∈ ball (0 : ℂ) ρ, ‖w z‖ ≤ M * ‖g z‖) (p : ℝ≥0∞) :
    ∃ A : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n),
      MemLp A p (volume.restrict (ball 0 1)) ∧
      ∀ z ∈ closedBall (0 : ℂ) (ρ / 2), ∀ r : EuclideanSpace ℂ (Fin n),
        ∑ i, g z i * A z r i = ∑ i, w z i * r i := by
  sorry

end JHolomorphic
