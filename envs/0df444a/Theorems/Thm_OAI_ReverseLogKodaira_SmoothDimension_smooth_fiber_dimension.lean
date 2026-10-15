-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_fiber_dimension
-- name    : OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:11:13.264001+00:00
-- url     : https://prove2.me/theorems/c0e283ae-67f3-407e-b92e-ac0e79a6c52d
-- title:
--   Fibres of a morphism of smooth $K$-schemes over an open set where it is smooth are smooth of relative dimension $a-b$
-- statement:
--   Let $K$ be a field and let $X$ and $Y$ be schemes whose structure morphisms $s_X\colon X\to\operatorname{Spec}K$ and $s_Y\colon Y\to\operatorname{Spec}K$ are smooth of relative dimension $a$ and $b$, respectively. Let $f\colon X\to Y$ be a morphism over $K$, i.e. $s_Y\circ f=s_X$. Let $y\colon\operatorname{Spec}K\to Y$ be any morphism of schemes, and let $T$ be a **nonempty** scheme with morphisms $i\colon T\to X$ and $s_T\colon T\to\operatorname{Spec}K$ such that the square
--   $$
--   \begin{array}{ccc} T & \xrightarrow{\;i\;} & X \\ {\scriptstyle s_T}\big\downarrow & & \big\downarrow{\scriptstyle f} \\ \operatorname{Spec}K & \xrightarrow{\;y\;} & Y \end{array}
--   $$
--   is a pullback, so that $T\cong X\times_{Y,y}\operatorname{Spec}K$ is the fibre of $f$ over $y$. Finally, let $U\subseteq Y$ be an open subset containing the image of $y$ such that the restriction $f|_U\colon f^{-1}(U)\to U$ is smooth. Then
--   $$
--   b\le a\qquad\text{and}\qquad s_T\colon T\to\operatorname{Spec}K\ \text{ is smooth of relative dimension } a-b .
--   $$
--
--   This is the dimension count for fibres of a morphism between smooth $K$-schemes at points of the base over which the morphism is smooth: such a fibre is smooth of dimension $\dim X-\dim Y$. It is used to compute the dimension of the fibres of a fibration of smooth projective varieties over the complement of the boundary of the base.
--
--   **Formalization Note** Smoothness of a given relative dimension is Mathlib's `SmoothOfRelativeDimension`. The number $a-b$ is natural-number subtraction, but no truncation occurs because $b\le a$ is part of the conclusion. The morphism $y$ is not required to be a section of $s_Y$; the hypothesis on $U$ is that the range of $y$ is contained in $U$ and that $f$ restricted over $U$ is smooth.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean#L253-L294

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

theorem OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension {K : Type*} [Field K]
    {X Y T : Scheme} [Nonempty T]
    (sX : X ⟶ Spec (CommRingCat.of K)) (sY : Y ⟶ Spec (CommRingCat.of K))
    (a b : ℕ) [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) (h : f ≫ sY = sX)
    (y : Spec (CommRingCat.of K) ⟶ Y) (i : T ⟶ X) (sT : T ⟶ Spec (CommRingCat.of K))
    (sq : IsPullback i sT f y) (U : Y.Opens) (hy : Set.range y ⊆ U)
    (hf : Smooth (f ∣_ U)) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) sT := by sorry
