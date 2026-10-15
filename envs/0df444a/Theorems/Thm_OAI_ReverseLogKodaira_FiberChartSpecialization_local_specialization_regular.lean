-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_local_specialization_regular
-- name    : OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:00:06.901359+00:00
-- url     : https://prove2.me/theorems/e9327f45-9709-4bb2-aeb3-bab219367863
-- title:
--   The fibre specialization of a log form, multiplied by the $m$-th power of its denominator, is regular on the fibre chart
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field and $\mathcal{O}_Z(W)$ the ring of sections over an open set $W$. A *reduced simple normal crossing (SNC) boundary* $E$ on $Z$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim Z-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_Z(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries. A *boundary fibration* $f\colon(X,E)\to(Y,D)$ is a surjective morphism $f\colon X\to Y$ over $\mathbb{C}$ whose fibres $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$ over all complex points $y$ are connected and which satisfies $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$; no smoothness is assumed. A *complex point* $y\in Y(\mathbb{C})$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$. For an open set $V\subseteq X$ that meets the fibre, i.e. $i^{-1}(V)\neq\emptyset$, and for $g\in\mathcal{O}_X(V)$, write $g|_F\in K(F)$ for the image of $i^{*}g\in\mathcal{O}_F(i^{-1}(V))$ in the function field of $F$ (its germ at the generic point of $F$).
--
--   Let $f\colon(X,E)\to(Y,D)$ be a boundary fibration, $y\in Y(\mathbb{C})$ a complex point and $(F,i,E_F)$ a fibre model of $f$ over $y$; put $r:=\dim F$. Let $U\subseteq Y$ be an affine open with $y\in U$, let $A:=\mathcal{O}_Y(U)$ and let $\mathrm{ev}_y\colon A\to\mathbb{C}$ be evaluation at $y$. Let $V\subseteq f^{-1}(U)$ be an affine open of $X$ that meets the fibre, put $B:=\mathcal{O}_X(V)$, an $A$-algebra via $f$, and let $W:=i^{-1}(V)\neq\emptyset$, which is an affine open of $F$ because $F$ is a fibre product.
--
--   Assume that $A\to B$ is formally smooth, and fix $n,m\in\mathbb{N}$, an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/\mathbb{C}}$, a $B$-basis $c$ of $\Omega_{B/A}$ with $r=\dim F$ elements, and $t\in B$ with $t|_F\neq0$. We use the following objects.
--   1. $\theta_b\colon\bigwedge^{n+r}_B\Omega_{B/\mathbb{C}}\to\bigwedge^{r}_B\Omega_{B/A}$ is the $B$-linear isomorphism characterised by $\theta_b\big(f^{*}\beta_1\wedge\cdots\wedge f^{*}\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for all $z_k\in\Omega_{B/\mathbb{C}}$ with images $\bar z_k\in\Omega_{B/A}$, where $f^{*}\beta_k$ is the image of $\beta_k$ in $\Omega_{B/\mathbb{C}}$; it is built from the exact sequence $0\to B\otimes_A\Omega_{A/\mathbb{C}}\to\Omega_{B/\mathbb{C}}\to\Omega_{B/A}\to0$ (exact on the left because $A\to B$ is formally smooth) and the bases $b$ and $c$.
--   2. $\rho\colon\Omega_{B/A}\to\Omega_{K(F)/\mathbb{C}}$, $dg\mapsto d(g|_F)$, is the map of differentials induced by the commutative square formed by $A\to B$, $\mathrm{ev}_y$, $g\mapsto g|_F$ and $\mathbb{C}\to K(F)$.
--   3. For $q\in P_B:=\big(\bigwedge^{n+r}_B\Omega_{B/\mathbb{C}}\big)^{\otimes_B m}$, the *fibre specialization* of the logarithmic form with denominator $t$ and numerator $q$ is $\operatorname{sp}_{b,c}(t;q):=(t|_F)^{-m}\cdot\big(\bigwedge^r\rho\circ\theta_b\big)^{\otimes m}(q)$, an element of $\omega^m_{K(F)}:=\big(\bigwedge^{r}_{K(F)}\Omega_{K(F)/\mathbb{C}}\big)^{\otimes m}$.
--   4. The *regular lattice* $L^F_m(W)\subseteq\omega^m_{K(F)}$ is the $\mathcal{O}_F(W)$-submodule spanned by all forms $\bigotimes_{j=1}^{m}\big(da_{j,1}\wedge\cdots\wedge da_{j,r}\big)$ with $a_{j,i}\in\mathcal{O}_F(W)$ (viewed in $K(F)$).
--
--   Then for every $q\in P_B$,
--
--   $$
--   (t|_F)^{m}\cdot\operatorname{sp}_{b,c}(t;q)\in L^F_m(W).
--   $$
--
--   Equivalently, the form $\big(\bigwedge^r\rho\circ\theta_b\big)^{\otimes m}(q)$ on the fibre is regular on the chart $W$. When $t$ is a local equation of $E$ on $V$, its pullback generates the ideal of $E_F$ on $W$, so the statement says that the fibre specialization of a logarithmic form has at most logarithmic poles along $E_F$ on this chart. This is the regularity input for showing that the restriction of a log pluricanonical form to a fibre is again a log pluricanonical form.
--
--   **Formalization Note** The fibre specialization is `logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q`, the regular lattice is `F.variety.regularPluriformLattice` on the affine open $W$ (its affineness comes from `fiber_affine_chart_pushout`), and $g\mapsto g|_F$ is `chartToFunctionField F.inclusion V`. The $A$-algebra structure on $B$ is a local instance, and the statement quantifies over the proof of formal smoothness. The inverse is taken in the field $K(F)$, and the hypothesis $t|_F\neq0$ makes it a genuine inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/FiberCharts.lean#L158-L225

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
open SmoothProjectiveVariety DifferentialBaseChange

theorem OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), chartToFunctionField F.inclusion V.1 t ≠ 0 →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (n + F.variety.dimension) m,
        (chartToFunctionField F.inclusion V.1 t)^m •
          logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q ∈
        F.variety.regularPluriformLattice
          ⟨F.inclusion ⁻¹ᵁ V.1, (fiber_affine_chart_pushout f y F U hy V e).1⟩ m := by sorry
