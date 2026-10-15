-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_BasedRelativeCanonical_based_relative_canonical_naturality
-- name    : OAI.ReverseLogKodaira.BasedRelativeCanonical.based_relative_canonical_naturality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:55:54.663581+00:00
-- url     : https://prove2.me/theorems/5d1f0a96-9650-4056-9290-591cc3f380cf
-- title:
--   Naturality of the relative canonical isomorphism $\Omega^{n+r}_{B/R}\cong\Omega^{r}_{B/A}$ along a map of formally smooth $A$-algebras $B\to C$
-- statement:
--   For a homomorphism of commutative rings $R\to A$ write $\Omega_{A/R}$ for the module of Kähler differentials, $d\colon A\to\Omega_{A/R}$ for the universal derivation, $\Omega^n_{A/R}:=\bigwedge^n_A\Omega_{A/R}$ for its $n$-th exterior power and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product of $\Omega^n_{A/R}$ over $A$.
--
--   For ring homomorphisms $R\to A\to B$ with $A\to B$ formally smooth, an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/R}$ and a $B$-basis $c$ of $\Omega_{B/A}$ with $r$ elements, let $\theta^B_{b,c}\colon\Omega^{n+r}_{B/R}\xrightarrow{\ \sim\ }\Omega^r_{B/A}$ be the *relative canonical isomorphism*. It is obtained from the short exact sequence $0\to B\otimes_A\Omega_{A/R}\to\Omega_{B/R}\to\Omega_{B/A}\to0$ through the determinant isomorphism $\bigwedge^n_B(B\otimes_A\Omega_{A/R})\otimes_B\Omega^r_{B/A}\cong\Omega^{n+r}_{B/R}$ adapted to the bases $1\otimes b$ and $c$, followed by the trivialisation of $\bigwedge^n_B(B\otimes_A\Omega_{A/R})$ given by the determinant coordinate of $1\otimes b$. Informally, $\theta^B_{b,c}$ deletes the factor $\beta_1\wedge\cdots\wedge\beta_n$ pulled back from $A$ and projects the remaining factors to relative differentials.
--
--   Let $R,A,B,C$ be commutative rings with ring homomorphisms $R\to A$, $A\to B$, $A\to C$, $B\to C$, $R\to B$, $R\to C$ such that all triangles commute: the composites $R\to A\to B$, $R\to A\to C$, $A\to B\to C$ and $R\to B\to C$ equal the given maps $R\to B$, $R\to C$, $A\to C$ and $R\to C$, respectively. Assume that $A\to B$ and $A\to C$ are formally smooth. Let $n,r\in\mathbb{N}$, let $b$ be an $A$-basis of $\Omega_{A/R}$ with $n$ elements, $c$ a $B$-basis of $\Omega_{B/A}$ with $r$ elements and $d$ a $C$-basis of $\Omega_{C/A}$ with $r$ elements. Let
--   $$\varphi_R\colon\Omega^{n+r}_{B/R}\to\Omega^{n+r}_{C/R},\qquad\varphi_A\colon\Omega^{r}_{B/A}\to\Omega^{r}_{C/A}$$
--   be the $B$-linear maps induced on exterior powers by $\Omega_{B/R}\to\Omega_{C/R}$ and $\Omega_{B/A}\to\Omega_{C/A}$, $dg\mapsto d\bar g$ ($\bar g$ the image of $g\in B$ in $C$). Then
--   $$
--   \theta^C_{b,d}\circ\varphi_R=\varphi_A\circ\theta^B_{b,c}\qquad\text{as }B\text{-linear maps }\Omega^{n+r}_{B/R}\to\Omega^r_{C/A}.
--   $$
--
--   The relative canonical isomorphism is thus compatible with every map $B\to C$ of formally smooth $A$-algebras, for instance the restriction map from the coordinate ring of an affine chart to that of a smaller chart. Taking $C=B$ with the identity map shows in particular that $\theta^B_{b,c}$ does not depend on the choice of the basis $c$ of $\Omega_{B/A}$, only on $b$. This is the compatibility needed to compare restrictions of forms to a fibre computed on different charts.
--
--   **Formalization Note** $\theta^B_{b,c}$ is `basedRelativeCanonicalEquiv R A B n r b c`, $\varphi_R$ is `exteriorDifferentialMap R R B C (n + r)` and $\varphi_A$ is `exteriorDifferentialMap A A B C r`. The $C$-linear map $\theta^C_{b,d}$ is regarded as $B$-linear by restriction of scalars. Bases are indexed by `Fin n` and `Fin r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/RelativeCanonical.lean#L283-L312

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.BasedRelativeCanonical
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open CanonicalAdjunction DifferentialBaseChange

theorem OAI.ReverseLogKodaira.BasedRelativeCanonical.based_relative_canonical_naturality
    (R A B C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [Algebra B C] [IsScalarTower A B C] [IsScalarTower R B C]
    [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A C]
    (n r : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (d : Module.Basis (Fin r) C (KaehlerDifferential A C)) :
    ((basedRelativeCanonicalEquiv R A C n r b d).toLinearMap.restrictScalars B).comp
        (exteriorDifferentialMap R R B C (n + r)) =
      (exteriorDifferentialMap A A B C r).comp
        (basedRelativeCanonicalEquiv R A B n r b c).toLinearMap := by sorry
