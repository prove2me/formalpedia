-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_haar_homotopy_invariant
-- name    : OAI.ArnoldCounterexample.CriticalBound.haar_homotopy_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:29:49.49698+00:00
-- url     : https://prove2.me/theorems/16c784ff-c028-4034-8159-8662ce39df7f
-- title:
--   Haar integrals of a closed cylinder form over $O(5)$ do not depend on the time slice
-- statement:
--   Let $O(5)\subset M_5(\mathbb{R})$ be the orthogonal group with right-invariant Haar measure $\mu$, and let $X_0,\dots,X_5$ be the six skew generators $R_{02},R_{12},R_{03},R_{13},R_{04},R_{14}$. Let $\Theta$ be a smooth $6$-form on the cylinder $\mathbb{R}\times M_5(\mathbb{R})$ that is closed, $d\Theta=0$. Assume the bracket condition: for all $t$, all $A\in O(5)$ and all $i<j$, the slice contraction $\sigma_t=\iota_{\partial_t}\Theta(t,\cdot)$ vanishes on
--   $$
--   \bigl(A[X_i,X_j],\ AX_k\ (k\ne i,j)\bigr).
--   $$
--   Then for all $a,b\in\mathbb{R}$,
--   $$
--   \int_{O(5)}\Theta(a,A)\bigl((0,AX_0),\dots,(0,AX_5)\bigr)\,d\mu(A)=\int_{O(5)}\Theta(b,A)\bigl((0,AX_0),\dots,(0,AX_5)\bigr)\,d\mu(A).
--   $$
--
--   Integrating a closed form over the orbit frame of $O(5)$ gives a quantity invariant under homotopy. This is the invariant that distinguishes the two ends of the join homotopy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Volume.lean#L21-L69

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

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
universe uE uF
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open ArnoldCounterexample.Forms ContinuousAlternatingMap
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_3

theorem OAI.ArnoldCounterexample.CriticalBound.haar_homotopy_invariant
    (Θ : ℝ × RM → (ℝ × RM) [⋀^Fin 6]→L[ℝ] ℝ)
    (hΘ : ContDiff ℝ ∞ Θ) (hclosed : ∀ p, extDeriv Θ p = 0)
    (hvertical : ∀ (t : ℝ) (A : O5) (i j : Fin 5),
      sliceContraction Θ t A
        (Matrix.vecCons ((A : RM) * (generators i.castSucc * generators j.succ -
          generators j.succ * generators i.castSucc))
          (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * generators k)))) = 0)
    (a b : ℝ) :
    (∫ A : O5, Θ (a, A) (fun i ↦ (0, (A : RM) * generators i)) ∂haar) =
    (∫ A : O5, Θ (b, A) (fun i ↦ (0, (A : RM) * generators i)) ∂haar) := by sorry
