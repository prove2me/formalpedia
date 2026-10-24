-- Prove2me | Theorems.Thm_OAI_SobolevBand_smooth_dyadic_bound
-- name    : OAI.SobolevBand.smooth_dyadic_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:40:27.507732+00:00
-- url     : https://prove2.me/theorems/354bf00b-040f-4a61-8d4c-afa491776b82
-- title:
--   Signed finite-band estimate for centered disk averages on dyadic radius ranges (OpenAI centered disk maximal operator, Proposition 1.2)
-- statement:
--   **Notation** (definitions bundle `OAIQWCDE000` of this split). The plane is $\mathbb C$. For $g : \mathbb C \to \mathbb R$, $x \in \mathbb C$ and $t > 0$, the signed disk average `signedAverage g x t` is
--   $$A_t g(x) = \frac{1}{\pi t^2}\int_{B(x,t)} g(y)\,dy .$$
--   For $0 < a \le b$, the band `band g a b` is the envelope $S_{a,b}\,g(x) = \sup_{a \le t \le b} A_t g(x)$ (`envelope`), and `gradient` is the Fréchet gradient.
--
--   **The statement.** There is an absolute constant $C > 0$ such that for every $C^1$ function $f : \mathbb C \to \mathbb R$ with compact support, every $a > 0$ and every $m \in \mathbb N$,
--   $$\int_{\mathbb C} \bigl\lVert \nabla S_{a,\,2^{m+1}a}\, f \bigr\rVert\,dx \;\le\; C\int_{\mathbb C} \lVert\nabla f\rVert\,dx .$$
--
--   This is the paper's Proposition 1.2 (the signed finite-band estimate) for radius ranges $[a, b]$ with $b/a = 2^{m+1}$, and for $C^1$ rather than $C^\infty$ compactly supported inputs. The constant does not depend on $a$ or on the number of dyadic scales.
--
--   Lean: `OAI.SobolevBand.smooth_dyadic_bound`, OpenAI's lemma of that name (in `lean/OAI/Analysis/DiskMaximal/WeakLimits.lean`).
-- source:
--   OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 085; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/DiskMaximal/WeakLimits.lean (declaration OAI.SobolevBand.smooth_dyadic_bound)

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

namespace SobolevBand
open DiskMoments RadiusEnvelope SignedRuns GeometricFilter DyadicHats ActualLabels

lemma smooth_dyadic_bound : ∃ C : ℝ, 0<C ∧ ∀ {f : ℂ → ℝ}, ContDiff ℝ 1 f →
    HasCompactSupport f → ∀ {a : ℝ}, 0<a → ∀ m : ℕ,
    (∫ x,‖gradient (band f a (2*((2:ℝ)^m*a))) x‖) ≤ C*(∫ x,‖gradient f x‖) := by
  sorry

end SobolevBand

end

end OAI
end
