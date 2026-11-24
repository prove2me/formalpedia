-- Prove2me | Theorems.Thm_HodgeComputer_PolarizedK3Remainder_certificate_defect
-- name    : HodgeComputer.PolarizedK3Remainder.certificate_defect
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:43:49.69661+00:00
-- url     : https://prove2.me/theorems/f6bf8d36-a0e0-423f-84c7-e639c6211271
-- title:
--   Polarized K3 remainder: cleared normal-chart certificate defect
-- statement:
--   For the exact sextic $F$ and source $A=X_0 X_1 X_2 Y_0 Y_1 Y_2$ of the [polarized-k3-remainder](https://hodge.computer/#case/polarized-k3-remainder) instance, with pole parameter $q=1$, there exist a denominator $S\in\mathbb C[z_0,\ldots,z_5]$, five numerator components $W_1,\ldots,W_5$, and a polynomial $Q$ such that
--
--   $$S\neq 0,\qquad S\ \text{is homogeneous of degree }e=\deg S,\qquad \operatorname{IsRelPrime}(F,S),$$
--   $$W_j\ \text{is homogeneous of degree }e+1\ \ (1\le j\le5),$$
--
--   and the key equation of the certificate framework holds in its cleared form,
--
--   $$\operatorname{defect}\bigl(F,A,D,1,N\bigr)=F^{2}Q,\qquad D=PS,\quad N_0=AS-\sum_{j\le5}(\partial_jF)W_j,\quad N_j=PW_j .$$
--
--   Here $\operatorname{defect}(F,A,D,q,N)=A D^2-qD\,N(F)+F\bigl(D\operatorname{div}(N)-N(D)\bigr)$, so the displayed identity is the condition that the rational vector field $N/D$ carries the target $A$ with a pole of order $q=1$.
--
--   This is the exact open content of the certificate problem for this instance. The source records existence as not established by the cited methods: the involution is a **block swap** $\tau(U,V)=(V,U)$ rather than a block sign, so the all-target block-sign theorem does not apply, and the projected numerator $B(U)-B(V)$ with $B(U)=\tfrac1{64}U_0^2U_1^2U_2^2$ reaches the remaining K3 exterior-square summand $\Lambda^2 H^2(w^2=f)_{\mathrm{prim}}$ rather than a supported elliptic sector (see [why.md](https://github.com/hodge-computer/sextics/blob/main/data/polarized-k3-remainder/why.md) and Chapter 3A §§3A.4–3A.6).
-- source:
--   https://hodge.computer/#case/polarized-k3-remainder ; https://github.com/hodge-computer/sextics/blob/main/data/polarized-k3-remainder/why.md ; docs/03a-split-and-k3.md §§3A.4–3A.6 ; Diamond arXiv:2603.29157

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.PolarizedK3Remainder

theorem HodgeComputer.PolarizedK3Remainder.certificate_defect :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W) = F ^ 2 * Q := by sorry
