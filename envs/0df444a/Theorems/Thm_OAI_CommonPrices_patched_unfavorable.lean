-- Prove2me | Theorems.Thm_OAI_CommonPrices_patched_unfavorable
-- name    : OAI.CommonPrices.patched_unfavorable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:40:12.89785+00:00
-- url     : https://prove2.me/theorems/c75b8d88-8a33-4d31-b3d2-a05f11dbc13d
-- title:
--   Unfavorable directional derivatives of disk averages, weighted by the label laws, cost O(‖∇g‖₁) over all scales (OpenAI centered disk maximal operator, Section 4)
-- statement:
--   **Notation** (definitions bundle `OAIQWCDE000` of this split). $A_t g(x)$ is the disk average `signedAverage g x t` (see `OAI.SobolevBand.smooth_dyadic_bound`), and `scale base j` is $2^j \cdot \mathrm{base}$.
--   - **Labels.** A `Label` is one of the finitely many unit directions $n \in \mathbb C$ of a fixed palette (`fixedPalette`). For a label $n$, `axis n s` $= \tfrac{\sqrt 3}{2} n + \tfrac{s}{2}\, i n$ for $s = \pm 1$ are the two unit vectors at angle $\pm 30°$ from $n$. The unfavorable part of a vector $z$ is
--   $$\texttt{unfavorable}\ n\ z = \bigl(-\langle \texttt{axis}\ n\ 1,\ z\rangle\bigr)_+ + \bigl(-\langle \texttt{axis}\ n\ (-1),\ z\rangle\bigr)_+ .$$
--   - **Radii.** A radius $t$ is a physical neighbourhood radius at scale $r$ for $g$ at $x$ (`PhysicalNeighborhoodRadius g r x t`) when $t \in [r, 2r]$ and $A_s g(x) \le A_t g(x)$ for every $s > 0$ with $|s - t| \le r/4$.
--   - **Label laws.** For $h = \nabla g$, radii $r_0, r_1, \dots$ and a level $k$, `marginal h r k x` is a probability law on labels at the point $x$ (`Law`). It starts from `initial` at radius $r_0$ and moves one level at a time by the transition laws `row` (`move`), which switch toward the quantized local direction of $h$. Here the radii are `geometricRadii base m k` $= 2^m\,\mathrm{base}/2^k$.
--
--   **The statement.** There is an absolute constant $C > 0$ with the following property. Let $\mathrm{base} > 0$, $R \ge 0$ and $N$ with $R/\mathrm{base} + 1 \le N$. Let $g : \mathbb C \to \mathbb R$ be $C^1$ with integrable gradient, with $\nabla g = 0$ outside the closed disk of radius $R$, and with bounded derivative. Then there are functions $H_{j,n} : \mathbb C \to \mathbb R$, one for each level $j \in \mathbb N$ and label $n$, such that:
--   - each $H_{j,n}$ is nonnegative and integrable;
--   - for almost every $x$, and all $j$, $n$ and physical neighbourhood radii $t$ at scale `scale base j`, $\texttt{unfavorable}\ n\ \bigl(\nabla_x A_t g(x)\bigr) \le H_{j,n}(x)$;
--   - for all $m$ and $n$,
--   $$\sum_{j=0}^{m} \int_{\mathbb C} \texttt{marginal}\ (\nabla g)\ (\texttt{geometricRadii}\ \mathrm{base}\ m)\ (m - j)\ x\ n \cdot H_{j,n}(x)\,dx \;\le\; C\int_{\mathbb C}\lVert\nabla g\rVert .$$
--
--   This is the direction-cost half of the paper's proof of Proposition 1.2 (Section 4, with the packing of switch and derivative costs, Proposition 4.3): the derivative of the averages against the labelled directions is paid for, over all scales at once, by the total variation of $g$.
--
--   Lean: `OAI.CommonPrices.patched_unfavorable`, OpenAI's theorem of that name (in `lean/OAI/Analysis/DiskMaximal/BandBounds.lean`).
-- source:
--   OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 085; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/DiskMaximal/BandBounds.lean (declaration OAI.CommonPrices.patched_unfavorable)

import Mathlib
import Definitions.Def_OAIQWCDE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

theorem patched_unfavorable : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    ∃ H : ℕ → Label → ℂ → ℝ,
      (∀ j n x, 0 ≤ H j n x) ∧ (∀ j n, Integrable (H j n)) ∧
      (∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
        unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x) ∧
      (∀ m n, (∑ j ∈ range (m+1), ∫ x, marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) ≤
        C*(∫ y, ‖gradient g y‖)) := by
  sorry
end CommonPrices

end

end OAI
end
