-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_specialization_refinement
-- name    : OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:03:11.800605+00:00
-- url     : https://prove2.me/theorems/395debfb-095e-41a0-9730-8facec4d28f4
-- title:
--   Fibre specialization of log forms is compatible with shrinking the affine chart
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field and $\mathcal{O}_Z(W)$ the ring of sections over an open set $W$. A *reduced simple normal crossing (SNC) boundary* $E$ on $Z$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim Z-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_Z(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries. A *boundary fibration* $f\colon(X,E)\to(Y,D)$ is a surjective morphism $f\colon X\to Y$ over $\mathbb{C}$ whose fibres $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$ over all complex points $y$ are connected and which satisfies $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$; no smoothness is assumed. A *complex point* $y\in Y(\mathbb{C})$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$. For an open set $V\subseteq X$ that meets the fibre, i.e. $i^{-1}(V)\neq\emptyset$, and for $g\in\mathcal{O}_X(V)$, write $g|_F\in K(F)$ for the image of $i^{*}g\in\mathcal{O}_F(i^{-1}(V))$ in the function field of $F$ (its germ at the generic point of $F$).
--
--   Let $f\colon(X,E)\to(Y,D)$ be a boundary fibration, $y\in Y(\mathbb{C})$ a complex point and $(F,i,E_F)$ a fibre model of $f$ over $y$. Let $U\subseteq Y$ be an affine open with $y\in U$, let $A:=\mathcal{O}_Y(U)$ and let $\mathrm{ev}_y\colon A\to\mathbb{C}$ be evaluation at $y$. Let $V'\subseteq V\subseteq f^{-1}(U)$ be nonempty affine opens of $X$ that both meet the fibre, and put $B:=\mathcal{O}_X(V)$ and $B':=\mathcal{O}_X(V')$, both $A$-algebras via $f$. The statement involves the following constructions, for a nonempty affine open $V''\in\{V,V'\}$ with ring $B'':=\mathcal{O}_X(V'')$ and $n,r,m\in\mathbb{N}$.
--   1. $\pi_{V''}\colon\big(\bigwedge^{n+r}_{B''}\Omega_{B''/\mathbb{C}}\big)^{\otimes_{B''}m}\to\big(\bigwedge^{n+r}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ is the $B''$-linear map induced by the germ map $B''\to K(X)$. For $t\in B''$ and a numerator $q$, the rational form $t^{-m}\pi_{V''}(q)$ is the *logarithmic pullback*.
--   2. Given an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/\mathbb{C}}$, formal smoothness of $A\to B''$ and a $B''$-basis $c''$ of $\Omega_{B''/A}$ with $r$ elements, $\theta^{V''}_b\colon\bigwedge^{n+r}_{B''}\Omega_{B''/\mathbb{C}}\to\bigwedge^r_{B''}\Omega_{B''/A}$ is the $B''$-linear isomorphism characterised by $\theta^{V''}_b\big(f^{*}\beta_1\wedge\cdots\wedge f^{*}\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ (with $\bar z_k$ the image of $z_k\in\Omega_{B''/\mathbb{C}}$ in $\Omega_{B''/A}$), built from the exact sequence $0\to B''\otimes_A\Omega_{A/\mathbb{C}}\to\Omega_{B''/\mathbb{C}}\to\Omega_{B''/A}\to0$ and the bases $b$, $c''$. Further, $\rho_{V''}\colon\Omega_{B''/A}\to\Omega_{K(F)/\mathbb{C}}$, $dg\mapsto d(g|_F)$, is induced by the commutative square formed by $A\to B''$, $\mathrm{ev}_y$, $g\mapsto g|_F$ and $\mathbb{C}\to K(F)$.
--   3. The *fibre specialization* of the logarithmic form with denominator $t\in B''$ and numerator $q$ is
--   $\operatorname{sp}^{V''}_{b,c''}(t;q):=(t|_F)^{-m}\cdot\big(\bigwedge^r\rho_{V''}\circ\theta^{V''}_b\big)^{\otimes m}(q)\in\big(\bigwedge^{r}_{K(F)}\Omega_{K(F)/\mathbb{C}}\big)^{\otimes m}$.
--
--   **Theorem.** Assume $A\to B$ and $A\to B'$ are formally smooth. Let $n,r,m\in\mathbb{N}$, let $b$ be an $A$-basis of $\Omega_{A/\mathbb{C}}$ with $n$ elements, $c$ a $B$-basis of $\Omega_{B/A}$ and $c'$ a $B'$-basis of $\Omega_{B'/A}$, both with $r$ elements, and let $t\in B$ and $t'\in B'$ with $t|_F\neq0$ and $t'|_F\neq0$. Then for all numerators $q\in\big(\bigwedge^{n+r}_B\Omega_{B/\mathbb{C}}\big)^{\otimes_B m}$ and $q'\in\big(\bigwedge^{n+r}_{B'}\Omega_{B'/\mathbb{C}}\big)^{\otimes_{B'} m}$,
--
--   $$
--   t^{-m}\,\pi_V(q)=t'^{-m}\,\pi_{V'}(q')\quad\Longrightarrow\quad \operatorname{sp}^{V}_{b,c}(t;q)=\operatorname{sp}^{V'}_{b,c'}(t';q').
--   $$
--
--   Thus the specialization to the fibre of a rational logarithmic form is unchanged when the chart $V$ is replaced by a smaller chart $V'$, when the basis of relative differentials is changed, and when a different denominator and numerator represent the same rational form. Together with the existence of common smaller charts, this makes the restriction of a log pluricanonical form to a fibre independent of all choices except the basis $b$.
--
--   **Formalization Note** The logarithmic pullback is `logarithmicPullback` into the pluriforms of the function field of $X$, and the fibre specialization is `logarithmicNumerator f y F U hy V e hsm n r m b c t`. The $A$-algebra structures on $B$ and $B'$ are local instances, and the statement quantifies over the proofs of formal smoothness. No relation between $c$ and $c'$ is assumed, and $r$ need not equal $\dim F$. Negative powers are field inverses (Lean sets $0^{-1}=0$); since $t|_F\neq0$ forces $t\neq0$, and the germ map of the integral scheme $X$ is injective on nonempty opens, all inverses are genuine.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/FiberCharts.lean#L266-L342

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

theorem OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V V' : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1) (hV : V'.1 ≤ V.1)
    [Nonempty V.1] [Nonempty V'.1]
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] [Nonempty (F.inclusion ⁻¹ᵁ V'.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V'.1) :=
      (f.hom.appLE U.1 V'.1 (hV.trans e)).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (hsm' : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V'.1))
      (n r m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin r) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (c' : Module.Basis (Fin r) Γ(X.scheme, V'.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V'.1)))
      (t : Γ(X.scheme, V.1)) (t' : Γ(X.scheme, V'.1)),
      chartToFunctionField F.inclusion V.1 t ≠ 0 →
      chartToFunctionField F.inclusion V'.1 t' ≠ 0 →
      ∀ (q : Pluricanonical ℂ Γ(X.scheme, V.1) (n+r) m)
        (q' : Pluricanonical ℂ Γ(X.scheme, V'.1) (n+r) m),
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField (n+r) m t q =
        logarithmicPullback ℂ Γ(X.scheme, V'.1) X.scheme.functionField (n+r) m t' q' →
      logarithmicNumerator f y F U hy V e hsm n r m b c t q =
        logarithmicNumerator f y F U hy V' (hV.trans e) hsm' n r m b c' t' q' := by sorry
