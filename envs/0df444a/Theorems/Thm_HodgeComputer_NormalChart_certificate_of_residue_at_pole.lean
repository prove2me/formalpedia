-- Prove2me | Theorems.Thm_HodgeComputer_NormalChart_certificate_of_residue_at_pole
-- name    : HodgeComputer.NormalChart.certificate_of_residue_at_pole
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T03:50:33.774796+00:00
-- url     : https://prove2.me/theorems/f1878bd3-662c-48a3-a0c0-f25bd510feb6
-- title:
--   The scalar normal-chart equation constructs certificates at every positive pole order
-- statement:
--   Let $q\ge1$, let $F$ be a nonzero homogeneous sextic in six complex variables, and let $A$ be homogeneous of degree $6q$. Put $P=\partial_0F$ and assume $P\ne0$ and $\operatorname{IsRelPrime}(F,P)$. Let $S\ne0$ be homogeneous of degree $e=\deg S$ and relatively prime to $F$. Suppose $W_1,\ldots,W_5$ are homogeneous of degree $e+6q-5$, and $Q$ is any polynomial. Set $B=A/q$.
--
--   If the previously defined normal-chart residue satisfies
--
--   $$\mathcal R_{F,B}(S,W)=F^qQ,$$
--
--   then the following polynomials satisfy the full certificate predicate at pole order $q$:
--
--   $$D=PS,\qquad N_0=BS-\sum_{j=1}^5(\partial_jF)W_j,\qquad N_j=PW_j.$$
--
--   In particular, $D$ is legal, each $N_i$ is homogeneous of degree $\deg D+6q-5$, and
--
--   $$AD^2-qD\,dF(N)+F\bigl(D\operatorname{div}N-dD(N)\bigr)=F^{q+1}Q.$$
--
--   There is no upper bound on $e$, and the remainder $Q$ need not vanish. This extends the pole-one normal-chart construction without imposing a strict-certificate restriction.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, normalized equations E1 and E2; derived formal product-rule construction for every positive pole order.

import Definitions.Def_HodgeComputerNormalChart
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


set_option autoImplicit false
open HodgeComputer HodgeComputer.NormalChart MvPolynomial

theorem HodgeComputer.NormalChart.certificate_of_residue_at_pole (q : ℕ) (hq : 0 < q)
    (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) (Q : AmbientPoly 5)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous 6) (hAhom : A.IsHomogeneous (6 * q))
    (hP : normal F ≠ 0) (hFP : IsRelPrime F (normal F))
    (hS : S ≠ 0) (hShom : S.IsHomogeneous S.totalDegree) (hFS : IsRelPrime F S)
    (hWhom : ∀ j, (W j).IsHomogeneous (S.totalDegree + (6 * q - 5)))
    (hres : residue F (MvPolynomial.C ((q : ℂ)⁻¹) * A) S W = F ^ q * Q) :
    Verify F A 6 q (denominator F S)
      (numerator F (MvPolynomial.C ((q : ℂ)⁻¹) * A) S W) Q := by sorry
