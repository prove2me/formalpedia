-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_sum_norm_sq_compLp_innerSL_408915f
-- name    : FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:31:25.50577+00:00
-- url     : https://prove2.me/theorems/6867a178-d7d2-4ce9-81f7-777183fca9ab
-- title:
--   Parseval Identity for Vector-Valued $L^2$ Components
-- statement:
--   This statement gives Parseval's identity in vector-valued $L^2$.
--
--   Let $(\alpha,\mu)$ be a measurable space with measure $\mu$, let $G$ be a real inner-product normed space, let $\iota$ be a finite index type, and let $b=(b_k)_{k\in\iota}$ be an orthonormal basis of $G$. For any $g\in L^2(\mu;G)$, take the scalar component $(x\mapsto\langle b_k,g(x)\rangle)$ for each basis vector. Then
--
--   $$\sum_{k\in\iota}\left\|\langle b_k,\,g(\cdot)\rangle\right\|_{L^2(\mu)}^2=\|g\|_{L^2(\mu;G)}^2.$$
--
--   This is the componentwise identity used to transfer scalar estimates to finite-dimensional vector-valued data.
--
--   **Formalization Note:** The components are represented by `(innerSL ℝ (b k)).compLp g`; the equality is in real $L^2$ and requires only a measurable space for the underlying measure.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/Components.lean#L58-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.Components`, declaration `FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL_408915f {μ : Measure α} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ G) (g : Lp G 2 μ) :
    ∑ k, ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 = ‖g‖ ^ 2 := by sorry
