-- Prove2me | Theorems.Thm_OAI_Paper256_tangent_coordinates_isomorphism
-- name    : OAI.Paper256.tangent_coordinates_isomorphism
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:39:34.991166+00:00
-- url     : https://prove2.me/theorems/126da8fb-fda2-4d1a-90d6-db7d455d379f
-- title:
--   The wedge coordinates $v_0h_i-h_0v_i$ identify the tangent space $v^{\perp}$ with $\mathbb{R}^3$
-- statement:
--   Let $v\in\mathbb{R}^4$, with coordinates $v_0,v_1,v_2,v_3$, be a unit vector ($\|v\|=1$ in the Euclidean norm) with $v_0\neq0$, and let
--   $$
--   T_v=\{h\in\mathbb{R}^4:\ \langle v,h\rangle=0\}
--   $$
--   be the tangent space of the unit sphere at $v$. For $h\in\mathbb{R}^4$ define the wedge coordinates
--   $$
--   w(v,h)=\big(v_0h_1-h_0v_1,\ v_0h_2-h_0v_2,\ v_0h_3-h_0v_3\big)\in\mathbb{R}^3 .
--   $$
--
--   **Theorem.** There is a linear isomorphism $J:T_v\to\mathbb{R}^3$ such that
--   $$
--   J(h)=w(v,h)\qquad\text{for all } h\in T_v .
--   $$
--   Equivalently, the linear map $h\mapsto w(v,h)$ restricted to $T_v$ is a bijection onto $\mathbb{R}^3$.
--
--   The vector $w(v,h)$ consists of the components of $v\wedge h$ that involve the coordinate $0$. Wedge coordinates of this kind arise when quadratic forms of matrices built from $vv^{\mathsf T}$ are evaluated on tangent vectors. The isomorphism converts statements quantified over all tangent directions $h\in T_v$ into statements quantified over all vectors of $\mathbb{R}^3$.
--
--   **Formalization Note** $\mathbb{R}^4$ is `Vec 4 = EuclideanSpace ℝ (Fin 4)`, $T_v$ is `tangentSpace v`, the kernel of $h\mapsto\langle v,h\rangle$, and $w$ is `wedgeCoordinates`, whose components are indexed by `Fin 3` with $i\mapsto i+1$ selecting the coordinates $1,2,3$ of $\mathbb{R}^4$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/TangentBasic.lean#L43-L83

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

open OAI OAI.Paper256
open scoped RealInnerProductSpace

theorem OAI.Paper256.tangent_coordinates_isomorphism (v : Vec 4) (hv : ‖v‖ = 1) (hv0 : v 0 ≠ 0) :
    ∃ J : tangentSpace v ≃ₗ[ℝ] (Fin 3 → ℝ),
      ∀ h : tangentSpace v, J h = wedgeCoordinates v h.val := by sorry
