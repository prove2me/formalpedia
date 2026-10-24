-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_radialExtension_radial_limit_408915f
-- name    : FunctionalInequalities.Analysis.radialExtension_radial_limit_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:22.539779+00:00
-- url     : https://prove2.me/theorems/351d76e3-ab94-494d-8147-25870d680af1
-- title:
--   Radial Extension Has Its Radial Limit
-- statement:
--   This private auxiliary lemma establishes radial continuity of a convex radial extension.
--
--   Let $E$ be finite-dimensional over $\mathbb R$, let $K\subseteq E$ be open with $0\in K$, and let $g:E\to\mathbb R$ be convex on $K$. Assume:
--
--   1. $g(x)\ge0$ for every $x\in K$.
--   2. $g(0)=0$.
--
--   For every $x\in E$, the radial extension `radialExtension K g` satisfies
--   $$\operatorname{radialExtension}(K,g)(tx)\longrightarrow\operatorname{radialExtension}(K,g)(x)$$
--   as $t\to1$ from below.
--
--   This is an internal continuity property used in constructing extended-real convex limits.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/RadialExtension.lean#L208-L262 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.RadialExtension`, declaration `_private.FunctionalInequalities.Analysis.Convex.RadialExtension.0.FunctionalInequalities.Analysis.radialExtension_radial_limit`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open Set Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section NormedSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]

lemma FunctionalInequalities.Analysis.radialExtension_radial_limit_408915f {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0) (x : E) :
    Tendsto (fun t : ℝ => FunctionalInequalities.Analysis.radialExtension K g (t • x)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (FunctionalInequalities.Analysis.radialExtension K g x)) := by sorry
