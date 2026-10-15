-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_LogarithmicSpecialization_logarithmic_specialization_equation_independent
-- name    : OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:25.568667+00:00
-- url     : https://prove2.me/theorems/bd6fcd79-474e-4a83-841d-b7ba8fc37415
-- title:
--   Logarithmic specialization depends only on the rational log form, not on its denominator and numerator
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative $R$-algebra and $B$ a commutative $A$-algebra (an $R$-algebra through $A$) such that $B$ is an integral domain and $A\to B$ is formally smooth. Let $K$ be the fraction field of $B$, an $R$-algebra through $B$. Let $S$ be a commutative $A$-algebra and let $C$ be a field equipped with ring homomorphisms $A\to C$, $B\to C$ and $S\to C$ such that both composites $A\to B\to C$ and $A\to S\to C$ equal $A\to C$; write $\bar g\in C$ for the image of $g\in B$. Fix $n,r,m\in\mathbb{N}$, an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/R}$ and a $B$-basis $c=(c_1,\dots,c_r)$ of $\Omega_{B/A}$. The statement involves the following objects.
--   1. $P_B:=\big(\bigwedge^{n+r}_B\Omega_{B/R}\big)^{\otimes_B m}$ and $P_K:=\big(\bigwedge^{n+r}_K\Omega_{K/R}\big)^{\otimes_K m}$, and the $B$-linear map $\pi\colon P_B\to P_K$ induced by $B\to K$ on differentials, exterior powers and tensor powers. For $t\in B$ and $u\in P_B$, the *logarithmic pullback* of $u$ with denominator $t$ is $t^{-m}\pi(u)\in P_K$.
--   2. $\theta_b\colon\bigwedge^{n+r}_B\Omega_{B/R}\to\bigwedge^{r}_B\Omega_{B/A}$, the $B$-linear isomorphism characterised by $\theta_b\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for all $z_k\in\Omega_{B/R}$, where $\tilde\beta_k$ is the image of $\beta_k$ in $\Omega_{B/R}$ and $\bar z_k$ the image of $z_k$ in $\Omega_{B/A}$. It is built from the exact sequence $0\to B\otimes_A\Omega_{A/R}\to\Omega_{B/R}\to\Omega_{B/A}\to0$ (exact on the left because $A\to B$ is formally smooth) and the bases $b$ and $c$.
--   3. $\rho\colon\Omega_{B/A}\to\Omega_{C/S}$, $dg\mapsto d\bar g$, the map of differentials induced by the commutative square, and the *specialization* $\mathrm{Sp}_{b,c}\colon P_B\to\big(\bigwedge^r_C\Omega_{C/S}\big)^{\otimes_C m}$, the $B$-linear map $\omega_1\otimes\cdots\otimes\omega_m\mapsto\bigotimes_{j=1}^m\big(\bigwedge^r\rho\big)\big(\theta_b(\omega_j)\big)$. For $t\in B$ and $u\in P_B$, the *logarithmic specialization* of $u$ with denominator $t$ is $\bar t^{-m}\,\mathrm{Sp}_{b,c}(u)$.
--
--   **Theorem.** Let $t,v\in B$ with $\bar t\neq0$ and $\bar v\neq0$ in $C$, and let $u,w\in P_B$. If $t^{-m}\pi(u)=v^{-m}\pi(w)$ in $P_K$, then
--
--   $$
--   \bar t^{-m}\,\mathrm{Sp}_{b,c}(u)=\bar v^{-m}\,\mathrm{Sp}_{b,c}(w)\qquad\text{in }\big(\textstyle\bigwedge^r_C\Omega_{C/S}\big)^{\otimes_C m}.
--   $$
--
--   In the geometric application, $A$ and $B$ are the coordinate rings of affine charts of the base and of the total space of a fibration, $S=\mathbb{C}$, $C$ is the function field of a fibre and the denominator is a local equation of the boundary. A logarithmic pluricanonical form is represented on the chart as a quotient $t^{-m}\pi(u)$, and the theorem says that its specialization to the fibre depends only on this quotient, not on the particular denominator and numerator chosen to represent it.
--
--   **Formalization Note** The logarithmic pullback is `logarithmicPullback R B K (n + r) m t`, the specialization is `specializePluricanonical R A B S C n r m b c`, and the logarithmic specialization is `logarithmicSpecialize R A B S C n r m b c t`; the isomorphism $\theta_b$ is `basedRelativeCanonicalEquiv R A B n r b c`. The negative powers are field inverses in $K$ and $C$ (Lean sets $0^{-1}=0$), but the hypotheses make them genuine: $\bar t\neq0$ forces $t\neq0$ in $B$, hence $t\neq0$ in $K$, and likewise for $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/Specialization.lean#L352-L406

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.LogarithmicSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

theorem OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent
    (R A B K S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Field K] [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsDomain B] [IsFractionRing B K] [Algebra.FormallySmooth A B]
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) (t v : B)
    (ht : algebraMap B C t ≠ 0) (hv : algebraMap B C v ≠ 0)
    (u w : Pluricanonical R B (n + r) m)
    (heq : logarithmicPullback R B K (n + r) m t u =
      logarithmicPullback R B K (n + r) m v w) :
    logarithmicSpecialize R A B S C n r m b c t u =
      logarithmicSpecialize R A B S C n r m b c v w := by sorry
