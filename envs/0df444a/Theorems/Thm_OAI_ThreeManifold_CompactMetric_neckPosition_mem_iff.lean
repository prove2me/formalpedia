-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_neckPosition_mem_iff
-- name    : OAI.ThreeManifold.CompactMetric.neckPosition_mem_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:14:52.065814+00:00
-- url     : https://prove2.me/theorems/fc49c552-ca5b-4824-9fbd-c3629ab37e2e
-- title:
--   The open neck is exactly where the neck-position height lies strictly between $0$ and $1$
-- statement:
--   Let $\Sigma=\mathbb{H}/\Gamma$ be the cusped hyperbolic surface of the construction, with its height function $\operatorname{ht}:\Sigma\to\mathbb{R}$, $\operatorname{ht}(\pi(z))=\log\max_{g\in\Gamma}\operatorname{Im}(g z)$, so that for $a>1$ the cusp region $\{\operatorname{Im} z>a\}$ projects onto $\{\operatorname{ht}>\log a\}$. The *piece* is $P=\{x\in\Sigma:\operatorname{ht}(x)<\log 8\}\times\mathbb{R}/6\mathbb{Z}$, and its *collar* is $\mathcal{C}=\{(x,\theta)\in P:\operatorname{ht}(x)>\log 2\}$. The 3-manifold $M$ is obtained from two copies of $P$, with inclusions $\iota_0,\iota_1:P\to M$, by identifying $\iota_0(w)$ with $\iota_1(\phi(w))$ for $w\in\mathcal{C}$, where $\phi$ is the fixed gluing homeomorphism of the collar. The *open neck* is $\mathcal{N}=\iota_0(\mathcal{C})$, which equals $\iota_1(\mathcal{C})$. With the *extended piece* $P'=\{(x,\theta)\in P:\operatorname{ht}(x)>1/2\}$, the *extended neck* is $\mathcal{N}'=\iota_0(P')\cup\iota_1(P')$.
--
--   For a parameter $\delta\in\mathbb{R}$, the *neck position map* $\nu_\delta:M\to\mathbb{R}\times(\mathbb{R}/6\mathbb{Z})^2$ is defined on each copy of $P$ through the logarithmic cusp coordinates, followed by a radial reparametrisation (which depends on $\delta$ on the first copy; on the second copy, the radial coordinate is also reflected, $t\mapsto 1-t$). The two definitions agree on the glued collar. On the extended neck its first coordinate is
--   $$
--   \nu_\delta(\iota_0(w))_1=\frac{\operatorname{ht}(x)-\log 2}{\log 4},\qquad \nu_\delta(\iota_1(w))_1=1-\frac{\operatorname{ht}(x)-\log 2}{\log 4}\qquad(w=(x,\theta)\in P').
--   $$
--
--   **Theorem.** For every $\delta\in\mathbb{R}$ and every point $p\in\mathcal{N}'$ of the extended neck,
--   $$
--   \nu_\delta(p)_1\in(0,1)\iff p\in\mathcal{N}.
--   $$
--
--   Thus, inside the region where neck coordinates are defined, the open neck is cut out by the condition $0<t<1$ on the height coordinate $t$. This lets one detect from the coordinate $t$ alone when a curve enters or leaves the neck, e.g. when analysing geodesic passages through it.
--
--   **Formalization Note** In Lean, $M$ is `GluedConstruction.Manifold`, $\nu_\delta$ is `neckPosition δ`, $\mathcal{N}$ is `openNeck` and $\mathcal{N}'$ is `extendedNeck`. The first coordinate is `.1` of a point of `Cylinder = ℝ × (AddCircle 6 × AddCircle 6)`. The displayed formulas are the inline lemma `piecePosition_height`; they rely on the fact that the radial reparametrisation equals $r\mapsto(r-\log 2)/\log 4$ for $r\ge 1/2$, whatever the value of $\delta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L228-L251

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages

open OAI OAI.ThreeManifold OAI.ThreeManifold.CompactMetric
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
open MetricConstruction CylinderConstruction GluedConstruction

theorem OAI.ThreeManifold.CompactMetric.neckPosition_mem_iff (δ : ℝ) {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    (neckPosition δ p).1 ∈ Ioo (0:ℝ) 1 ↔ p ∈ openNeck := by sorry
