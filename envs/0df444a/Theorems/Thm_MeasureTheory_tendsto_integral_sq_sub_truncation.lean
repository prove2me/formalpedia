-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_integral_sq_sub_truncation
-- name    : MeasureTheory.tendsto_integral_sq_sub_truncation
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:28:24.318077+00:00
-- url     : https://prove2.me/theorems/857c17b7-ce17-4394-a78b-f67def6585ec
-- title:
--   The L² truncation error of a square-integrable function vanishes
-- statement:
--   **Truncation converges in $L^2$.** If $f$ is measurable and $f^2$ is integrable, and $f_K$ denotes $f$ clipped to $[-K, K]$, then
--   $$\int (f - f_K)^2 \, d\pi \;\longrightarrow\; 0 \qquad (K \to \infty).$$
--
--   This is the statement that bounded functions are dense in $L^2$, in the concrete form given by truncation, which is the form used when a theorem proved for bounded observables is extended to square-integrable ones. The clipping map $y \mapsto \max(\min(y,K), -K)$ is chosen because it is simultaneously a contraction towards $0$ (so $|f - f_K| \le |f|$, giving the domination) and eventually the identity at each fixed point (so the pointwise limit is $0$).
--
--   **Proof.** Dominated convergence. For the domination, an inspection of the three cases $|y| \le K$, $y > K$, $y < -K$ gives $|y - \max(\min(y,K),-K)| \le |y|$ whenever $K \ge 0$, hence $(f - f_K)^2 \le f^2$, which is integrable by hypothesis. For the pointwise limit, fix $x$ and choose $K_0 > |f(x)|$; for every $K \ge K_0$ the clipping leaves $f(x)$ unchanged, so the integrand is eventually identically $0$ at $x$.
-- source:
--   W. Rudin, Real and Complex Analysis, 3rd ed., McGraw-Hill 1987, Chapter 3 (density of simple/bounded functions in Lp); P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Section 16.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MeasureTheory.tendsto_integral_sq_sub_truncation {X : Type*} [MeasurableSpace X]
    (π : Measure X) [IsProbabilityMeasure π]
    (f : X → ℝ) (hf : Measurable f) (hL2 : Integrable (fun x => (f x) ^ 2) π) :
    Tendsto (fun K : ℕ => ∫ x, (f x - max (min (f x) (K : ℝ)) (-(K : ℝ))) ^ 2 ∂π)
      atTop (𝓝 0) := by sorry
