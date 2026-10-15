-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_dimension_unique
-- name    : OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:04.722484+00:00
-- url     : https://prove2.me/theorems/d7606b2d-0960-4bec-b920-baf5c084791d
-- title:
--   A nonempty smooth scheme over a field has a unique relative dimension
-- statement:
--   A ring homomorphism $R\to S$ is *standard smooth of relative dimension $d$* if $S\cong R[x_1,\dots,x_N]/(g_1,\dots,g_k)$ with $N-k=d$ and, after renumbering the variables, the Jacobian determinant $\det\big(\partial g_i/\partial x_j\big)_{1\le i,j\le k}$ is a unit in $S$. A morphism of schemes $g\colon X\to Y$ is *smooth of relative dimension $d$* if every point $x\in X$ has an affine open neighbourhood $V$ together with an affine open $U\subseteq Y$ such that $V\subseteq g^{-1}(U)$ and the ring homomorphism $\mathcal{O}_Y(U)\to\mathcal{O}_X(V)$ induced by $g$ is standard smooth of relative dimension $d$; it is *smooth* if the same holds with standard smooth ring maps whose relative dimension may depend on the point.
--
--   Let $K$ be a field, let $X$ be a **nonempty** scheme and let $f\colon X\to\operatorname{Spec}K$ be a morphism. If $f$ is smooth of relative dimension $n$ and also smooth of relative dimension $m$, then
--
--   $$
--   n=m .
--   $$
--
--   So the relative dimension of a smooth morphism from a nonempty scheme to the spectrum of a field is well defined. Nonemptiness is necessary, since the empty scheme is smooth of every relative dimension. The result is used to compare dimensions computed in two ways, for instance to identify the dimension of a fibre of a fibration and to derive the subtraction rule for relative dimensions.
--
--   **Formalization Note** Smoothness of a given relative dimension is Mathlib's `SmoothOfRelativeDimension`, and nonemptiness is the instance `Nonempty X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean#L14-L64

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

theorem OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique {K : Type*} [Field K]
    (X : Scheme) [Nonempty X] (f : X ⟶ Spec (CommRingCat.of K)) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by sorry
