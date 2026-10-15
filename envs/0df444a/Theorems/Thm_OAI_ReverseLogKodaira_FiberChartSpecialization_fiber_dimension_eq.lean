-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_fiber_dimension_eq
-- name    : OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:54:13.101702+00:00
-- url     : https://prove2.me/theorems/5cd7a5f4-cdb9-47f8-9516-9926b622c2c6
-- title:
--   Fibres of a stratum-smooth fibration away from the boundary have dimension $\dim X-\dim Y$
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field.
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$. Boundaries on other varieties, such as $D$ on $Y$ or $E_F$ on $F$ below, are defined in the same way.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries, and let $f\colon(X,E)\to(Y,D)$ be a *stratum-smooth fibration*: $f\colon X\to Y$ is a surjective morphism over $\mathbb{C}$ whose fibres $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$ over all complex points $y$ are connected, with $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$, such that over $Y^{\circ}:=Y\setminus\operatorname{Supp}D$ both $f$ and its restriction to every stratum of $E$ (the closed subscheme cut out by $\sum_{i\in S}\mathcal{I}_{E_i}$, for each nonempty set $S$ of components) are smooth. A *complex point* $y\in Y(\mathbb{C})$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$.
--
--   If the complex point $y$ lies in $Y^{\circ}=Y\setminus\operatorname{Supp}D$, then every fibre model $(F,i,E_F)$ of $f$ over $y$ satisfies
--   $$
--   \dim X=\dim Y+\dim F .
--   $$
--
--   This dimension identity is what allows forms of degree $\dim X$ on $X$ to be split into a part of degree $\dim Y$ coming from the base and a part of degree $\dim F$ along the fibre; it is a standing hypothesis in the construction that restricts log pluricanonical forms to fibres.
--
--   **Formalization Note** The dimensions are the relative dimensions recorded in the structures (`X.dimension`, `Y.dimension`, `F.variety.dimension`), and $Y^{\circ}$ is `D.complement`, the complement of the support of the ideal sheaf of $D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean#L93-L110

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

theorem OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (y : Y.ComplexPoint)
    (hy : y.point ∈ D.complement) (F : FiberModel f.toBoundaryFibration y) :
    X.dimension = Y.dimension + F.variety.dimension := by sorry
