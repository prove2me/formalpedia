-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_logarithmicNumerator_ne_zero_of_coefficient
-- name    : OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:05:43.410421+00:00
-- url     : https://prove2.me/theorems/ea186cc9-8af3-476f-b94d-823f189ab932
-- title:
--   Nonvanishing criterion for the fibre specialization of a pluricanonical numerator
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field.
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$. Boundaries on other varieties are defined in the same way.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries, and let $f\colon(X,E)\to(Y,D)$ be a *boundary fibration*: a surjective morphism over $\mathbb{C}$ whose fibres over all complex points are connected and with $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$ (no smoothness is assumed). A *complex point* $y\in Y(\mathbb{C})$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$. Write $\omega^m_{K(F)}=\big(\textstyle\bigwedge^{\dim F}_{K(F)}\Omega_{K(F)/\mathbb{C}}\big)^{\otimes m}$ for the rational $m$-pluricanonical forms on $F$.
--
--   Let $U\subseteq Y$ be an affine open with $y\in U$ and $A:=\mathcal{O}_Y(U)$, and let $V\subseteq f^{-1}(U)$ be an affine open of $X$ that meets the fibre ($i^{-1}(V)\neq\emptyset$), with $B:=\mathcal{O}_X(V)$ regarded as an $A$-algebra via $f$. Put $r=\dim F$, let $n,m\in\mathbb{N}$ and let $b=(\beta_1,\dots,\beta_n)$ be an $A$-basis of $\Omega_{A/\mathbb{C}}$. For $g\in B$ write $g|_F\in K(F)$ for the image of $i^{*}g\in\mathcal{O}_F(i^{-1}V)$ in the function field of $F$. Let $\rho\colon\Omega_{B/A}\to\Omega_{K(F)/\mathbb{C}}$, $dg\mapsto d(g|_F)$, be the map of differentials induced by the commutative square formed by $A\to B$, evaluation $A\to\mathbb{C}$ at $y$, restriction $B\to K(F)$ and $\mathbb{C}\to K(F)$. When $A\to B$ is formally smooth, let $\theta_b\colon\bigwedge^{n+r}_B\Omega_{B/\mathbb{C}}\to\bigwedge^{r}_B\Omega_{B/A}$ be the $B$-linear isomorphism characterised by $\theta_b\big(f^{*}\beta_1\wedge\cdots\wedge f^{*}\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for $z_k\in\Omega_{B/\mathbb{C}}$ with images $\bar z_k\in\Omega_{B/A}$; it comes from the exact sequence $0\to B\otimes_A\Omega_{A/\mathbb{C}}\to\Omega_{B/\mathbb{C}}\to\Omega_{B/A}\to0$ and the trivialisation of $\bigwedge^n_A\Omega_{A/\mathbb{C}}$ given by $b$. For a $B$-basis $c=(c_1,\dots,c_r)$ of $\Omega_{B/A}$ let $\det_c\colon\bigwedge^r_B\Omega_{B/A}\to B$ be the coordinate with $\det_c(c_1\wedge\cdots\wedge c_r)=1$, and let $\kappa_{b,c}\colon\big(\bigwedge^{n+r}_B\Omega_{B/\mathbb{C}}\big)^{\otimes_B m}\to B$ be the $B$-linear isomorphism $\kappa_{b,c}(\omega_1\otimes\cdots\otimes\omega_m)=\prod_{j}\det_c\big(\theta_b(\omega_j)\big)$. Equivalently, every $q$ in the source satisfies $q=\kappa_{b,c}(q)\cdot\big(f^{*}\beta_1\wedge\cdots\wedge f^{*}\beta_n\wedge\tilde c_1\wedge\cdots\wedge\tilde c_r\big)^{\otimes m}$ for any lifts $\tilde c_k\in\Omega_{B/\mathbb{C}}$ of the $c_k$.
--
--   Assume that $A\to B$ is formally smooth, and let $c$ be a $B$-basis of $\Omega_{B/A}$ indexed by $r=\dim F$ elements, let $t\in B$ with $t|_F\neq0$, and let $q\in\big(\bigwedge^{n+r}_B\Omega_{B/\mathbb{C}}\big)^{\otimes_B m}$. Then
--   $$
--   \kappa_{b,c}(q)|_F\neq0\quad\Longrightarrow\quad (t|_F)^{-m}\cdot\big(\textstyle\bigwedge^r\rho\circ\theta_b\big)^{\otimes m}(q)\neq0\ \text{ in }\omega^m_{K(F)} .
--   $$
--
--   The form on the right is the specialization to the fibre $F$ of the log form $t^{-m}q$. The criterion says that whether this specialization vanishes is detected by one regular function on the chart, namely the coefficient $\kappa_{b,c}(q)$. It is used to show that a nonzero log pluricanonical form restricts to nonzero forms on all fibres meeting the locus where this coefficient does not vanish.
--
--   **Formalization Note** The specialized form is `logarithmicNumerator f y F U hy V e hsm n (F.variety.dimension) m b c t q` and $\kappa_{b,c}$ is `pluricanonicalCoordinate`; the restriction $g\mapsto g|_F$ is `chartToFunctionField F.inclusion V`. The statement introduces the $A$-algebra structure on $B$ and its compatibility with $\mathbb{C}$ by local instances and quantifies over the formal smoothness proof, $n$, $m$, $b$, $c$, $t$ and $q$. The inverse is taken in $K(F)$, and the hypothesis $t|_F\neq0$ makes it a genuine inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/NonzeroFiber.lean#L134-L198

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

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

theorem OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1)),
      letI := hsm
      ∀ (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), chartToFunctionField F.inclusion V.1 t ≠ 0 →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (n + F.variety.dimension) m,
        chartToFunctionField F.inclusion V.1
          (pluricanonicalCoordinate ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1)
            n F.variety.dimension m b c q) ≠ 0 →
        logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q ≠ 0 := by sorry
