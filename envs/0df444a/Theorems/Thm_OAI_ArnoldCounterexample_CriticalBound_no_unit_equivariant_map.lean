-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_no_unit_equivariant_map
-- name    : OAI.ArnoldCounterexample.CriticalBound.no_unit_equivariant_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:33:10.458576+00:00
-- url     : https://prove2.me/theorems/98f9ceb0-0641-4448-9f72-6d564a9b3e01
-- title:
--   No smooth circle-equivariant map from the unit isotropic quadric to the unit sphere of $\mathbb{C}^3$
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $\pi:S\to Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$ is the projection. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0=\sum_jz_jv_j$. Let $|w|^2=\sum_{i<3}|w_i|^2$ on $\mathbb{C}^3$. There is no smooth map $F:\mathbb{C}^5\to\mathbb{C}^3$ such that for all $z\in S$
--   $$
--   |F(z)|^2=1\qquad\text{and}\qquad F(\alpha z)=\alpha\,F(z)\quad\text{for all }\alpha\in\mathbb{C},\ |\alpha|=1 .
--   $$
--
--   Topologically this is a cup-length obstruction: the third power of the symplectic class of $Q_3$ is nonzero, while an equivariant map to the unit sphere of $\mathbb{C}^3$ would force it to vanish. Combined with the cover-map construction, this forces at least four critical points for every smooth function on $Q_3$.
--
--   **Formalization Note** The theorem concludes `False` from the existence of such an $F$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Obstruction.lean#L178-L220

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open ArnoldCounterexample.Forms ContinuousAlternatingMap
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_5

theorem OAI.ArnoldCounterexample.CriticalBound.no_unit_equivariant_map (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) :
    False := by sorry
