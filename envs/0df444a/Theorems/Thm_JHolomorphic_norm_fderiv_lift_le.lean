-- Prove2me | Theorems.Thm_JHolomorphic_norm_fderiv_lift_le
-- name    : JHolomorphic.norm_fderiv_lift_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T22:39:09.510982+00:00
-- url     : https://prove2.me/theorems/26666ed6-aea1-4b34-96b1-7b98a1e3a288
-- title:
--   A pointwise bound for the derivative of the lift $z\mapsto(u(z),Du(z)e)$
-- statement:
--   Let $E$ be a real normed space, $u:\mathbb{C}\to E$, $z\in\mathbb{C}$ and $e\in\mathbb{C}$ with $|e|\le1$. Suppose that $u$ is differentiable at $z$ and that $Du:\mathbb{C}\to\mathcal{L}(\mathbb{C},E)$ is differentiable at $z$. Then the map $v(w)=\bigl(u(w),Du(w)e\bigr)$ satisfies
--   $$\|Dv(z)\|\le\|Du(z)\|+\|D^2u(z)\|.$$
--   This bound controls the first derivative of a tangent lift of $u$ by the first two derivatives of $u$.
--
--   **Formalization Note** The lift is `fun z => (u z, fderiv ℝ u z e)` with values in `E × E` (sup norm), and $D^2u(z)$ is `fderiv ℝ (fderiv ℝ u) z`. All norms are operator norms.
-- source:
--   Elementary differential calculus; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Normed.Operator.Prod

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- The derivative of the lift `z ↦ (u(z), Du(z) e)` with `‖e‖ ≤ 1` is bounded pointwise by
`‖Du(z)‖ + ‖D²u(z)‖`, wherever `u` and `Du` are differentiable. -/
theorem norm_fderiv_lift_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℂ → E)
    (z e : ℂ) (he : ‖e‖ ≤ 1) (hd1 : DifferentiableAt ℝ u z)
    (hd2 : DifferentiableAt ℝ (fderiv ℝ u) z) :
    ‖fderiv ℝ (fun z => (u z, fderiv ℝ u z e)) z‖ ≤
      ‖fderiv ℝ u z‖ + ‖fderiv ℝ (fderiv ℝ u) z‖ := by
  sorry

end JHolomorphic
