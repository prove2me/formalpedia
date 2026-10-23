-- Prove2me | Theorems.Thm_JHolomorphic_memLp_clm_apply_of_continuousOn
-- name    : JHolomorphic.memLp_clm_apply_of_continuousOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:33:25.391276+00:00
-- url     : https://prove2.me/theorems/fac9c1d1-89d6-418f-a0e1-f7c64a3aee9f
-- title:
--   Applying a continuous operator field preserves $L^p$ on a compact set
-- statement:
--   Let $K\subset\mathbb{C}$ be compact, $X,Y$ real normed spaces, $0<p\le\infty$, $B:\mathbb{C}\to\mathcal{L}_{\mathbb{R}}(X,Y)$ continuous on $K$, and $r\in L^p(K;X)$ (Lebesgue measure restricted to $K$). Then $z\mapsto B(z)\,r(z)$ belongs to $L^p(K;Y)$.
--
--   A basic closure property of local $L^p$ spaces under multiplication by continuous coefficients, used for products appearing in Cauchy–Riemann type equations.
--
--   **Formalization Note** Membership is `MemLp _ p (volume.restrict K)` with `p : ℝ≥0∞`; continuity is `ContinuousOn B K` in the operator-norm topology.
-- source:
--   Standard; Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- For a compact `K ⊆ ℂ`, an operator field `B` continuous on `K` and `r ∈ L^p(K)`, the map
`z ↦ B z (r z)` lies in `L^p(K)`. -/
theorem memLp_clm_apply_of_continuousOn {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {K : Set ℂ} (hK : IsCompact K) {p : ℝ≥0∞}
    {B : ℂ → X →L[ℝ] Y} (hB : ContinuousOn B K) {r : ℂ → X}
    (hr : MemLp r p (volume.restrict K)) : MemLp (fun z => B z (r z)) p (volume.restrict K) := by
  sorry

end JHolomorphic
