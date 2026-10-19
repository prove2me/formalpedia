-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_sphere_field_quadratic
-- name    : OAI.EuclideanRamsey.sphere_field_quadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:06:00.902312+00:00
-- url     : https://prove2.me/theorems/860f6497-6a3a-4c5b-93f9-ab97c2759e68
-- title:
--   A sphere through the points gives a kernel vector of the quadratic rows
-- statement:
--   Let $K\subseteq\mathbb R$ be the field generated over $\mathbb Q$ by all coordinates $a_{ij}$ of a configuration $a_0,\dots,a_{s-1}\in\mathbb R^d$. For each point let $\tilde a_i:\{0,1,\dots,d\}\to K$ be its augmented vector, $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$. The quadratic rows are the vectors $\bigl(\tilde a_i(p)\,\tilde a_i(q)\bigr)_{p,q\in\{0,\dots,d\}}\in K^{(d+1)^2}$. If all $a_i$ lie on a sphere $\{x:|x-c|=r\}$ in $\mathbb R^d$, then there is $h:\{0,\dots,d\}^2\to K$ with
--   $$
--   \sum_{p,q}\tilde a_i(p)\tilde a_i(q)\,h(p,q)=0\ \ \text{for every }i,\qquad h(j,k)=\delta_{jk}\ \ (1\le j,k\le d).
--   $$
--
--   The point is that $h$ has entries in the coordinate field $K$, even though the centre and radius of the sphere need not.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Quadratic.lean#L117-L166

import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Quadratic

open OAI OAI.EuclideanRamsey
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix

theorem OAI.EuclideanRamsey.sphere_field_quadratic {s d : ℕ} (a : Fin s → Space d)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    ∃ h : QuadraticIndex d → Coeff a,
      augmentedQuadraticRows a *ᵥ h = 0 ∧
      ∀ j k : Fin d, h (some j, some k) = if j = k then 1 else 0 := by sorry
