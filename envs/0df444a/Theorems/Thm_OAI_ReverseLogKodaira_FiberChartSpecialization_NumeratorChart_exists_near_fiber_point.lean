-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_NumeratorChart_exists_near_fiber_point
-- name    : OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:56:56.381035+00:00
-- url     : https://prove2.me/theorems/0fbc15b2-86d7-4b29-af8e-ca4943ecabfa
-- title:
--   Numerator charts exist near every point of a fibre over the open part of the base
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the one-dimensional $K(X)$-vector space of rational $m$-pluricanonical forms. For a nonempty affine open $W\subseteq X$, the *regular lattice* $L_m(W)\subseteq\omega^m_{K(X)}$ is the $\mathcal{O}_X(W)$-submodule spanned by all forms $\bigotimes_{j=1}^{m}\big(da_{j,1}\wedge\cdots\wedge da_{j,\dim X}\big)$ with $a_{j,i}\in\mathcal{O}_X(W)$ (viewed in $K(X)$).
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$. A form $s\in\omega^m_{K(X)}$ is a *log $m$-pluriform* for $(X,E)$ if $t^m s\in L_m(W)$ for every nonempty affine open $W$ and every nonzero $t\in\mathcal{O}_X(W)$ with $\mathcal{I}_E(W)=(t)$; these forms make up a $\mathbb{C}$-subspace $S_m(X,E)\subseteq\omega^m_{K(X)}$, the formal counterpart of $H^0\big(X,m(K_X+E)\big)$. The same notation ($\omega^m$, $L_m$, $S_m$, $\operatorname{Supp}$) is used for every smooth projective variety with a reduced SNC boundary, in particular for $(Y,D)$ and $(F,E_F)$ below.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries, and let $f\colon(X,E)\to(Y,D)$ be a *stratum-smooth fibration*: $f\colon X\to Y$ is a surjective morphism over $\mathbb{C}$ whose fibres $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$ over all complex points $y$ are connected, with $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$, such that over $Y^{\circ}:=Y\setminus\operatorname{Supp}D$ both $f$ and its restriction to every stratum of $E$ (the closed subscheme cut out by $\sum_{i\in S}\mathcal{I}_{E_i}$, for each nonempty set $S$ of components) are smooth. A *complex point* $y\in Y(\mathbb{C})$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$.
--
--   Fix an affine open $U\subseteq Y^{\circ}$ with $A:=\mathcal{O}_Y(U)$, a complex point $y\in U$, a fibre model $(F,i,E_F)$ of $f$ over $y$ such that $\dim X=\dim Y+\dim F$, an integer $m\in\mathbb{N}$ and a log $m$-pluriform $s\in S_m(X,E)$. A *numerator chart* for $s$ consists of
--   1. a nonempty affine open $V\subseteq f^{-1}(U)$ of $X$ that meets the fibre, i.e. $i^{-1}(V)\neq\emptyset$; put $B:=\mathcal{O}_X(V)$, an $A$-algebra via $f$;
--   2. the property that $A\to B$ is formally smooth, together with a $B$-basis $c=(c_1,\dots,c_{\dim F})$ of $\Omega_{B/A}$;
--   3. a nonzero $t\in B$ with $\mathcal{I}_E(V)=(t)$;
--   4. a *numerator* $q\in\big(\textstyle\bigwedge^{\dim Y+\dim F}_{B}\Omega_{B/\mathbb{C}}\big)^{\otimes_B m}$ with $t^{-m}\iota_V(q)=s$, where $\iota_V$ is the map to $\omega^m_{K(X)}$ induced by $B\to K(X)$ (degrees being identified through $\dim X=\dim Y+\dim F$).
--
--   For every open subset $O\subseteq X$ and every point $z\in F$ with $i(z)\in O$, there exists a numerator chart for $s$ whose affine open $V$ satisfies
--   $$
--   i(z)\in V\subseteq O .
--   $$
--
--   Numerator charts are the local data from which the restriction of $s$ to the fibre $F$ is computed. The result shows that they exist arbitrarily close to any point of the fibre; this is used both to define the restricted form independently of choices and to verify that it has logarithmic poles along $E_F$.
--
--   **Formalization Note** A numerator chart is the structure `NumeratorChart f y F U hdim m s`, where `hdim` is the hypothesis $\dim X=\dim Y+\dim F$; its fields are the affine open, the inclusion $V\subseteq f^{-1}(U)$, the two nonemptiness facts, formal smoothness, the relative basis, the equation $t$ with $t\neq0$ and $\mathcal{I}_E(V)=(t)$, the numerator $q$, and the identity relating $q$ to $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean#L135-L168

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

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

theorem OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (O : X.scheme.Opens) (z : F.variety.scheme) (hz : F.inclusion z ∈ O) :
    ∃ P : NumeratorChart f.toBoundaryFibration y F U hdim m s,
      F.inclusion z ∈ P.V.1 ∧ P.V.1 ≤ O := by sorry
