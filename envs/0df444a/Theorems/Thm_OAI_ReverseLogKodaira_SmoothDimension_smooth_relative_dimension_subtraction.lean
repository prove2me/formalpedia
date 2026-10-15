-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_relative_dimension_subtraction
-- name    : OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:07:02.650337+00:00
-- url     : https://prove2.me/theorems/bb06b8ab-638e-4494-9cc9-e57002deb38c
-- title:
--   Subtraction rule: a smooth morphism between smooth $K$-schemes of relative dimensions $a$ and $b$ has relative dimension $a-b$
-- statement:
--   A ring homomorphism $R\to S$ is *standard smooth of relative dimension $d$* if $S\cong R[x_1,\dots,x_N]/(g_1,\dots,g_k)$ with $N-k=d$ and, after renumbering the variables, the Jacobian determinant $\det\big(\partial g_i/\partial x_j\big)_{1\le i,j\le k}$ is a unit in $S$. A morphism of schemes $g\colon X\to Y$ is *smooth of relative dimension $d$* if every point $x\in X$ has an affine open neighbourhood $V$ together with an affine open $U\subseteq Y$ such that $V\subseteq g^{-1}(U)$ and the ring homomorphism $\mathcal{O}_Y(U)\to\mathcal{O}_X(V)$ induced by $g$ is standard smooth of relative dimension $d$; it is *smooth* if the same holds with standard smooth ring maps whose relative dimension may depend on the point.
--
--   Let $K$ be a field and let $X$ and $Y$ be schemes with $X$ **nonempty**. Suppose the morphism $s_X\colon X\to\operatorname{Spec}K$ is smooth of relative dimension $a$ and $s_Y\colon Y\to\operatorname{Spec}K$ is smooth of relative dimension $b$. Let $f\colon X\to Y$ be a smooth morphism over $K$, i.e. $s_Y\circ f=s_X$. Then
--
--   $$
--   b\le a\qquad\text{and}\qquad f\ \text{is smooth of relative dimension } a-b .
--   $$
--
--   This is the familiar rule $\dim X-\dim Y$ for the relative dimension of a smooth morphism between smooth varieties. It is used to determine the relative dimension of a fibration over the open part of the base where it is smooth, and from that the dimension of its fibres.
--
--   **Formalization Note** Smoothness of a given relative dimension is Mathlib's `SmoothOfRelativeDimension`, and plain smoothness is `Smooth`. The difference $a-b$ is natural-number subtraction, but no truncation occurs because $b\le a$ is part of the conclusion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean#L72-L121

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

theorem OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction {K : Type*} [Field K]
    {X Y : Scheme} [Nonempty X] (sX : X ⟶ Spec (CommRingCat.of K))
    (sY : Y ⟶ Spec (CommRingCat.of K)) (a b : ℕ)
    [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) [Smooth f] (h : f ≫ sY = sX) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) f := by sorry
