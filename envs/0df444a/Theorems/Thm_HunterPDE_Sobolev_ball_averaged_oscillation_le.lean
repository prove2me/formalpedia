-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_ball_averaged_oscillation_le
-- name    : HunterPDE.Sobolev.ball_averaged_oscillation_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T22:00:43.383171+00:00
-- url     : https://prove2.me/theorems/1d13bc3b-1765-49c1-b8b7-70046203f0af
-- title:
--   Local averaged oscillation bound for C1 functions when p exceeds dimension
-- statement:
--   Let $n\ge1$ and $n<p<\infty$, and set $\alpha=1-n/p$. There is a finite nonnegative constant $C=C(n,p)$ such that every continuously differentiable function $f:\mathbb R^n\to\mathbb R$, every ball $B(a,r)$ of positive radius, and every $x\in B(a,r)$ satisfy
--   $$\int_{B(a,r)} |f(x)-f(z)|\,dz\le |B(a,r)|\,C\,\|Df\|_{L^p(B(a,3r))}\,r^\alpha.$$
--   The constant is uniform in the function, center, radius, and interior point. No compact support is required. The formal statement uses extended nonnegative integrals and norms, so an infinite gradient norm is allowed.
--
--   The intended proof applies Hunter's centered segment-integration estimate on $B(x,2r)$ and Holder's inequality to the locally integrable kernel $|x-z|^{1-n}$. Since $B(a,r)\subset B(x,2r)\subset B(a,3r)$, the passage between normalized averages includes the volume ratio $2^n$. This ratio is absorbed into $C$. This is an Open analytic prerequisite, not an established proof.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, pp. 68–70, proof of Theorem 3.36, equation (3.14) and the following Holder estimate. Local off-center formulation obtained by enlarging B(a,r) to B(x,2r), retaining the volume ratio 2^n, and localizing gradients to B(a,3r).

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

theorem HunterPDE.Sobolev.ball_averaged_oscillation_le {n : ℕ} {p : ℝ}
    (hn : 0 < n) (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → ∀ (a : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ∀ x ∈ Metric.ball a r,
        (∫⁻ z in Metric.ball a r, ENNReal.ofReal |f x - f z|) ≤
          volume (Metric.ball a r) * (C : ENNReal) *
            eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball a (3 * r))) *
            ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by sorry
