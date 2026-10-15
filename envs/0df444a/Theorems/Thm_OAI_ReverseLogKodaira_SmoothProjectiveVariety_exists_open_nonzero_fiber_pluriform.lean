-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_exists_open_nonzero_fiber_pluriform
-- name    : OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:07:46.930204+00:00
-- url     : https://prove2.me/theorems/1f0d0a7d-98d8-4e4f-9fc8-1723059e6eb0
-- title:
--   A nonzero log pluricanonical form yields nonzero log pluricanonical forms on all fibres over a nonempty open set
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the one-dimensional $K(X)$-vector space of rational $m$-pluricanonical forms. For a nonempty affine open $W\subseteq X$, the *regular lattice* $L_m(W)\subseteq\omega^m_{K(X)}$ is the $\mathcal{O}_X(W)$-submodule spanned by all forms $\bigotimes_{j=1}^{m}\big(da_{j,1}\wedge\cdots\wedge da_{j,\dim X}\big)$ with $a_{j,i}\in\mathcal{O}_X(W)$ (viewed in $K(X)$).
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$. A form $s\in\omega^m_{K(X)}$ is a *log $m$-pluriform* for $(X,E)$ if $t^m s\in L_m(W)$ for every nonempty affine open $W$ and every nonzero $t\in\mathcal{O}_X(W)$ with $\mathcal{I}_E(W)=(t)$; these forms make up a $\mathbb{C}$-subspace $S_m(X,E)\subseteq\omega^m_{K(X)}$, the formal counterpart of $H^0\big(X,m(K_X+E)\big)$. The same notation ($\omega^m$, $L_m$, $S_m$, $\operatorname{Supp}$) is used for every smooth projective variety with a reduced SNC boundary, in particular for $(Y,D)$ and $(F,E_F)$ below.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries, and let $f\colon(X,E)\to(Y,D)$ be a *stratum-smooth fibration*: $f\colon X\to Y$ is a surjective morphism over $\mathbb{C}$ whose fibres $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$ over all complex points $y$ are connected, with $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$, such that over $Y^{\circ}:=Y\setminus\operatorname{Supp}D$ both $f$ and its restriction to every stratum of $E$ (the closed subscheme cut out by $\sum_{i\in S}\mathcal{I}_{E_i}$, for each nonempty set $S$ of components) are smooth. A *complex point* $y\in Y(\mathbb{C})$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$.
--
--   Let $m>0$ and let $s\in S_m(X,E)$ be a nonzero log $m$-pluriform. Then there exists a nonempty open subset $U\subseteq Y^{\circ}=Y\setminus\operatorname{Supp}D$ such that
--   $$
--   \forall\,y\in Y(\mathbb{C})\ \text{with}\ y\in U,\ \ \forall\ \text{fibre models }(F,i,E_F)\text{ of } f \text{ over } y:\qquad S_m(F,E_F)\neq\{0\}.
--   $$
--   That is, every such fibre carries a nonzero log $m$-pluriform for its boundary $E_F$.
--
--   In terms of log Kodaira dimension: if $(X,E)$ has a nonzero log pluricanonical form, then the fibres over a nonempty Zariski open subset of the base do too, so their log Kodaira dimension is not $-\infty$. This is the key input for the branch of the subadditivity analysis in which the general fibre has log Kodaira dimension $-\infty$.
--
--   **Formalization Note** The open set is an element `U` of `Y.scheme.Opens` with `U` different from the bottom element (nonempty) and contained in `D.complement`; $S_m(F,E_F)$ is `F.boundary.sections m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/NonzeroFiber.lean#L449-L522

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
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_NonzeroFiber

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open DifferentialBaseChange CanonicalSpecialization FiberChartSpecialization

theorem OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (m : ℕ) (hm : 0 < m)
    (s : X.RationalPluriform m) (hs : s ∈ E.sections m) (hn : s ≠ 0) :
    ∃ U : Y.scheme.Opens, U ≠ ⊥ ∧ U ≤ D.complement ∧
      ∀ (y : Y.ComplexPoint), y.point ∈ U →
        ∀ F : FiberModel f.toBoundaryFibration y,
          ∃ σ : F.variety.RationalPluriform m, σ ∈ F.boundary.sections m ∧ σ ≠ 0 := by sorry
