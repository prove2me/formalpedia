-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_RelativeCharts_exists_standard_chart_over_smooth_open
-- name    : OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:08:45.937781+00:00
-- url     : https://prove2.me/theorems/d911fdc3-e44e-4b84-81cb-90d9a9b2468c
-- title:
--   Standard smooth affine charts over a fixed affine open of the base exist inside every neighbourhood
-- statement:
--   A ring homomorphism $R\to S$ is *standard smooth of relative dimension $d$* if $S\cong R[x_1,\dots,x_N]/(g_1,\dots,g_k)$ with $N-k=d$ and, after renumbering the variables, the Jacobian determinant $\det\big(\partial g_i/\partial x_j\big)_{1\le i,j\le k}$ is a unit in $S$. A morphism of schemes $g\colon X\to Y$ is *smooth of relative dimension $d$* if every point $x\in X$ has an affine open neighbourhood $V$ together with an affine open $U\subseteq Y$ such that $V\subseteq g^{-1}(U)$ and the ring homomorphism $\mathcal{O}_Y(U)\to\mathcal{O}_X(V)$ induced by $g$ is standard smooth of relative dimension $d$; it is *smooth* if the same holds with standard smooth ring maps whose relative dimension may depend on the point.
--
--   Let $f\colon X\to Y$ be a morphism of schemes, $n\in\mathbb{N}$, and $U\subseteq Y$ an affine open such that the restriction $f|_U\colon f^{-1}(U)\to U$ is smooth of relative dimension $n$. Let $V\subseteq X$ be an open set and $x\in V$ a point with $f(x)\in U$. Then there exists an affine open $W\subseteq X$ with
--
--   $$
--   x\in W\subseteq V,\qquad W\subseteq f^{-1}(U),\qquad \mathcal{O}_Y(U)\xrightarrow{\;f^{*}\;}\mathcal{O}_X(W)\ \text{standard smooth of relative dimension } n .
--   $$
--
--   Compared with the definition of smoothness, the affine open of the base is prescribed to be $U$ itself, and the chart can be chosen inside any given neighbourhood of $x$. This is what allows one to choose affine charts adapted at the same time to the smooth structure of a fibration over a fixed base chart and to other local data, such as a local equation of a boundary divisor.
--
--   **Formalization Note** The restriction $f|_U$ is Mathlib's `f ∣_ U`, and the ring map is `f.appLE U W e` for the inclusion $e\colon W\subseteq f^{-1}(U)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean#L129-L177

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts

open OAI OAI.ReverseLogKodaira
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open
    {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)
    (U : Y.affineOpens) [SmoothOfRelativeDimension n (f ∣_ U.1)] (V : X.Opens) (x : X) (hx : x ∈ V)
    (hfx : f x ∈ U.1) :
    ∃ (W : X.affineOpens), x ∈ W.1 ∧ W.1 ≤ V ∧
      ∃ (e : W.1 ≤ f ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U.1 W.1 e).hom := by sorry
