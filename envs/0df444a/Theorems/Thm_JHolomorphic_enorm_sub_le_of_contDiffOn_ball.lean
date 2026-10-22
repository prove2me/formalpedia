-- Prove2me | Theorems.Thm_JHolomorphic_enorm_sub_le_of_contDiffOn_ball
-- name    : JHolomorphic.enorm_sub_le_of_contDiffOn_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T00:25:11.232988+00:00
-- url     : https://prove2.me/theorems/65bfc541-43ff-4079-a6c3-ec106946676f
-- title:
--   Oscillation of $C^1$ maps on a disc controlled by $\|Dg\|_{L^p}$, $p>2$
-- statement:
--   Let $E$ be a real Banach space and $p>2$. There is a constant $C$ such that for every disc $B(c,r)\subseteq\mathbb C$ ($r>0$), every map $g:\mathbb C\to E$ that is $C^1$ on $B(c,r)$, and all $z,w\in B(c,r)$,
--   $$\|g(z)-g(w)\|\le C\,r^{1-2/p}\,\|Dg\|_{L^p(B(c,r))}.$$
--   This is the oscillation form of Morrey's inequality in the plane; it gives uniform equicontinuity of families with bounded $L^p$ derivatives.
--
--   **Formalization Note** `ContDiffOn ℝ 1 g (ball c r)`; the bound is stated in `ℝ≥0∞`: `‖g z - g w‖ₑ ≤ ENNReal.ofReal (C * r ^ (1 - 2 / p)) * eLpNorm (fderiv ℝ g) (ENNReal.ofReal p) (volume.restrict (ball c r))`, with the operator norm on `fderiv ℝ g`.
-- source:
--   Morrey's inequality; L. C. Evans, Partial Differential Equations, §5.6.2, Theorem 4 and its proof; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Normed.Module.Convex

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- Oscillation bound on a disc for `p > 2`: there is `C` such that for every disc `B(c, r)`, every
map `g` that is `C¹` on `B(c, r)` and all `z, w ∈ B(c, r)`,
`‖g z - g w‖ ≤ C r^{1-2/p} ‖Dg‖_{L^p(B(c,r))}`. -/
theorem enorm_sub_le_of_contDiffOn_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiffOn ℝ 1 g (ball c r) →
      ∀ z ∈ ball c r, ∀ w ∈ ball c r, ‖g z - g w‖ₑ ≤
        ENNReal.ofReal (C * r ^ (1 - 2 / p)) *
          eLpNorm (fderiv ℝ g) (ENNReal.ofReal p) (volume.restrict (ball c r)) := by
  sorry

end JHolomorphic
