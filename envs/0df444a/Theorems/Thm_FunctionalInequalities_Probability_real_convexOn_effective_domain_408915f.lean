-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_real_convexOn_effective_domain_408915f
-- name    : FunctionalInequalities.Probability.real_convexOn_effective_domain_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:31.59002+00:00
-- url     : https://prove2.me/theorems/93f18973-140a-4e43-96f0-114622c301db
-- title:
--   Real Convexity On The Effective Domain
-- statement:
--   This statement extracts ordinary real convexity from an extended-real convex epigraph.
--
--   Let $E$ be a real inner-product normed additive group and let $\phi:E\to\overline{\mathbb R}$. Assume:
--
--   1. $\phi(x)\ge 0$ for every $x\in E$.
--   2. The real epigraph
--      $$\{(x,t)\in E\times\mathbb R:\phi(x)\le t\}$$
--      is convex.
--
--   Then the function $x\mapsto(\phi(x)).\operatorname{toReal}$ is `ConvexOn` on the effective domain
--   $$\{x\in E:\phi(x)\ne+\infty\}.$$
--
--   This is a technical bridge between extended-real convex potentials and ordinary real convex-analysis results.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L539-L559 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.real_convexOn_effective_domain`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Compact

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section PointControl
open Set
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma FunctionalInequalities.Probability.real_convexOn_effective_domain_408915f {φ : E → EReal} (h0 : ∀ x, 0 ≤ φ x)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
    ConvexOn ℝ {x | φ x ≠ ⊤} (fun x => (φ x).toReal) := by sorry
