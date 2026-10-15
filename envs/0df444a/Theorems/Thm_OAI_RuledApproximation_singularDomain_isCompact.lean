-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singularDomain_isCompact
-- name    : OAI.RuledApproximation.singularDomain_isCompact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:10:29.862962+00:00
-- url     : https://prove2.me/theorems/c4f8820f-9f36-4678-a2ab-09bb91e77954
-- title:
--   The singular base domain $\Omega_{p,\gamma,c}$ is compact
-- statement:
--   For real numbers $p$ and $b$ let
--
--   $$
--   \Delta_p(b)=b^2\Big(\frac p4+(2-p)\,b^2\Big)
--   $$
--
--   be the ceiling polynomial, and for real parameters $p,\gamma,c$ let $\Omega_{p,\gamma,c}\subseteq\mathbb{R}^2$ be the set of points $b=(b_0,b_1)$ satisfying
--
--   $$
--   c^\gamma\le b_1\le 2,\qquad |b_0|\le b_1,\qquad b_1\le \tfrac12+c^2\,\Delta_p(b_0)+c^{5/2}.
--   $$
--
--   **Theorem.** For all real numbers $p,\gamma,c$, the set $\Omega_{p,\gamma,c}$ is a compact subset of $\mathbb{R}^2$.
--
--   For small $c>0$ the set $\Omega_{p,\gamma,c}$ is a perturbation of the triangle $\{|b_0|\le b_1\le \tfrac12\}$: the part below height $c^\gamma$ is cut off and the top edge is replaced by the curve $b_1=\tfrac12+c^2\Delta_p(b_0)+c^{5/2}$, which lies above it when $0\le p\le2$ (then $\Delta_p\ge0$). It is the common base region of the two families of ruled pieces in the singular covering of the regular tetrahedron, and its compactness provides the measurability and finite area needed whenever areas or integrals over it are computed.
--
--   **Formalization Note** The set is `singularDomain p gamma c` and $\Delta_p$ is `ceilingPolynomial p`, on the Euclidean plane `Plane` with coordinates `b 0`, `b 1`. The powers $c^\gamma$ and $c^{5/2}$ are real powers (`Real.rpow`); no sign condition on $c$ is imposed (for $c\le0$ these powers follow Mathlib's convention), so the statement covers every real choice of the parameters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularBounds.lean#L69-L83

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.singularDomain_isCompact (p gamma c : ℝ) : IsCompact (singularDomain p gamma c) := by sorry
