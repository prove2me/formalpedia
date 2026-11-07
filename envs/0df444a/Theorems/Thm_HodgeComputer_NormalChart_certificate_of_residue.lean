-- Prove2me | Theorems.Thm_HodgeComputer_NormalChart_certificate_of_residue
-- name    : HodgeComputer.NormalChart.certificate_of_residue
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-06T23:04:39.180056+00:00
-- url     : https://prove2.me/theorems/ccb2e8a7-0648-46d8-992a-5dde2376aac5
-- title:
--   A scalar normal-chart residue equation constructs a sextic certificate
-- statement:
--   Let $F,A\in\mathbb C[z_0,\ldots,z_5]$ be homogeneous of degree six, with $F\ne0$. Put $P=\partial_0F$, and suppose $P\ne0$ and $\gcd(F,P)=1$. Let $S\ne0$ be homogeneous of degree $e=\deg S$, with $\gcd(F,S)=1$. Suppose each of $W_1,\ldots,W_5$ is homogeneous of degree $e+1$, and let $Q$ be any polynomial. Use the normal-chart definitions
--
--   $$D=PS,\qquad N_0=AS-\sum_{j=1}^5(\partial_jF)W_j,\qquad N_j=PW_j.$$
--
--   If the scalar residue equation holds, then these exact polynomials are a certificate:
--
--   $$\mathcal R_{F,A}(S,W)=FQ\quad\Longrightarrow\quad
--   \operatorname{Verify}(F,A,6,1,D,N,Q).$$
--
--   In particular, $D$ is nonzero, homogeneous and relatively prime to $F$, each $N_i$ has degree $\deg D+1$, and
--
--   $$AD^2-D\sum_{i=0}^5(\partial_iF)N_i+F\left(D\sum_{i=0}^5\partial_iN_i-\sum_{i=0}^5(\partial_iD)N_i\right)=F^2Q.$$
--
--   Write $z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)$, $F_i=\partial_i F$, $P=F_0$, and use subscripts on $P,S,A$ for partial derivatives. For five polynomials $W_1,\ldots,W_5$, define
--
--   $$
--   \begin{aligned}
--   \mathcal R_{F,A}(S,W)={}&S^2(PA_0-AP_0)\\
--   &+\sum_{j=1}^5\left[P^2S\,\partial_jW_j-PSF_j\,\partial_0W_j
--   +\bigl(F_j(SP_0+PS_0)-P(SP_j+PS_j)\bigr)W_j\right].
--   \end{aligned}
--   $$
--
--   This construction eliminates the gradient equation and leaves one scalar equation for five free numerator components. Zero components and a nonzero quotient $Q$ are allowed; the degree of $S$ has no upper bound.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, "One denominator and the normalized equations", E1 and E2; derived product-rule normal-chart construction.

import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.NormalChart MvPolynomial

theorem HodgeComputer.NormalChart.certificate_of_residue (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) (Q : AmbientPoly 5)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous 6) (hAhom : A.IsHomogeneous 6)
    (hP : normal F ≠ 0) (hFP : IsRelPrime F (normal F))
    (hS : S ≠ 0) (hShom : S.IsHomogeneous S.totalDegree) (hFS : IsRelPrime F S)
    (hWhom : ∀ j, (W j).IsHomogeneous (S.totalDegree + 1))
    (hres : residue F A S W = F * Q) :
    Verify F A 6 1 (denominator F S) (numerator F A S W) Q := by sorry
