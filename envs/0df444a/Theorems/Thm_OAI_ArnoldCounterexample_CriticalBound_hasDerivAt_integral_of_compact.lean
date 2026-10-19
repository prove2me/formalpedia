-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_hasDerivAt_integral_of_compact
-- name    : OAI.ArnoldCounterexample.CriticalBound.hasDerivAt_integral_of_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:17:58.441001+00:00
-- url     : https://prove2.me/theorems/63280a84-c0c5-44b6-a045-e23e29e2de73
-- title:
--   Differentiation under the integral sign over a compact space with a finite measure
-- statement:
--   Let $G$ be a compact topological space with its Borel $\sigma$-algebra and $\mu$ a finite measure on $G$. Let $F,F':\mathbb{R}\times G\to\mathbb{R}$ be jointly continuous, and suppose that for every $s\in\mathbb{R}$ and $g\in G$ the function $s\mapsto F(s,g)$ has derivative $F'(s,g)$. Then for every $t\in\mathbb{R}$,
--   $$
--   \frac{d}{ds}\Big|_{s=t}\int_GF(s,g)\,d\mu(g)=\int_GF'(t,g)\,d\mu(g).
--   $$
--
--   Compactness supplies the uniform domination that differentiation under the integral sign requires. The lemma is applied to integrals over the orthogonal group with respect to its Haar measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Haar.lean#L16-L37

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
universe uG
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped BigOperators
open MeasureTheory Set Filter

theorem OAI.ArnoldCounterexample.CriticalBound.hasDerivAt_integral_of_compact
    {G : Type uG} [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    {F F' : ℝ → G → ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ t g, HasDerivAt (fun s ↦ F s g) (F' t g) t) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ g, F s g ∂μ) (∫ g, F' t g ∂μ) t := by sorry
