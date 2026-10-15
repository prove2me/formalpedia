-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_exists_global_specialization
-- name    : OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:02:13.975356+00:00
-- url     : https://prove2.me/theorems/cb0dc06c-91eb-43ee-857a-781c6c4ea9ae
-- title:
--   Restricting a log pluricanonical form to a fibre: independence of charts and logarithmic poles
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
--   Put $n=\dim Y$ and $r=\dim F$, and fix an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/\mathbb{C}}$. For a numerator chart $P=(V,c,t,q)$ with $B=\mathcal{O}_X(V)$ we use the following maps. For $g\in B$ write $g|_F\in K(F)$ for the image of $i^{*}g\in\mathcal{O}_F(i^{-1}V)$ in the function field of $F$. Let $\rho\colon\Omega_{B/A}\to\Omega_{K(F)/\mathbb{C}}$, $dg\mapsto d(g|_F)$, be the map of differentials induced by the commutative square formed by $A\to B$, evaluation $A\to\mathbb{C}$ at $y$, restriction $B\to K(F)$ and $\mathbb{C}\to K(F)$. When $A\to B$ is formally smooth, let $\theta_b\colon\bigwedge^{n+r}_B\Omega_{B/\mathbb{C}}\to\bigwedge^{r}_B\Omega_{B/A}$ be the $B$-linear isomorphism characterised by $\theta_b\big(f^{*}\beta_1\wedge\cdots\wedge f^{*}\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for $z_k\in\Omega_{B/\mathbb{C}}$ with images $\bar z_k\in\Omega_{B/A}$; it comes from the exact sequence $0\to B\otimes_A\Omega_{A/\mathbb{C}}\to\Omega_{B/\mathbb{C}}\to\Omega_{B/A}\to0$ and the trivialisation of $\bigwedge^n_A\Omega_{A/\mathbb{C}}$ given by $b$. The *value* of $P$ is
--   $\sigma_P(b):=(t|_F)^{-m}\cdot\big(\textstyle\bigwedge^r\rho\circ\theta_b\big)^{\otimes m}(q)\in\omega^m_{K(F)}$.
--   Heuristically, $\sigma_P(b)$ is obtained from $s$ by dividing by $\big(f^{*}(\beta_1\wedge\cdots\wedge\beta_n)\big)^{\otimes m}$ and restricting to $F$, in the spirit of the adjunction $\omega_X\cong f^{*}\omega_Y\otimes\omega_{X/Y}$ followed by $\omega_{X/Y}|_F\cong\omega_F$.
--
--   Under these hypotheses there exists a form $\sigma\in\omega^m_{K(F)}$ such that
--   $$
--   \sigma\in S_m(F,E_F)\qquad\text{and}\qquad \sigma_P(b)=\sigma\ \text{ for every numerator chart } P \text{ for } s .
--   $$
--
--   So the chartwise restrictions of $s$ glue to a single, well-defined form on the fibre, and this form is again a log $m$-pluriform for the boundary $E_F$. This is how log $m$-pluriforms on $(X,E)$ are restricted to fibres over $Y^{\circ}$ (the result depends on the choice of $b$), the key step in comparing log pluricanonical forms on the total space with those on the fibres.
--
--   **Formalization Note** The value $\sigma_P(b)$ is `P.value hy b`, defined through `logarithmicNumerator`. The inverse $(t|_F)^{-m}$ is taken in the field $K(F)$, with Lean's convention that the inverse of $0$ is $0$; for numerator charts $t|_F$ is in fact nonzero. The basis $b$ is indexed by $\{0,\dots,\dim Y-1\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean#L231-L276

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
open SmoothProjectiveVariety DifferentialBaseChange

theorem OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) :
    ∃ σ : F.variety.RationalPluriform m, σ ∈ F.boundary.sections m ∧
      ∀ P : NumeratorChart f.toBoundaryFibration y F U hdim m s, P.value hy b = σ := by sorry
