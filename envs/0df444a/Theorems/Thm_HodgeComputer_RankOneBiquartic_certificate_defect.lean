-- Prove2me | Theorems.Thm_HodgeComputer_RankOneBiquartic_certificate_defect
-- name    : HodgeComputer.RankOneBiquartic.certificate_defect
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T10:35:32.523408+00:00
-- url     : https://prove2.me/theorems/2ddd951a-a312-4f7e-8900-ac244f4f5847
-- title:
--   A normal-chart certificate exists for the rank-one-biquartic instance
-- statement:
--   For the exact sextic $F$ and source $A=X_0^3Y_0^3$ of the rank-one-biquartic instance, with pole parameter $q=1$, there exist a denominator $S\in\mathbb C[z_0,\ldots,z_5]$, five numerator components $W_1,\ldots,W_5$, and a polynomial $Q$ such that
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
--   This is the exact content of the certificate problem for this instance, and it is open: the source records the existence of a certificate for this target as "not established by the cited methods", and the mixed coupling $t=\tfrac57$ removes the product decomposition on which the split-case theorem relies. The statement is deliberately formulated with the cleared defect rather than with the residue, so that the first normalized equation $N(F)=AD$ — which holds identically in the normal chart — is not an extra burden on the solver.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, section "One denominator and the normalized equations", equations (E1) and (E2); data/rank-one-biquartic/instance.rec; data/rank-one-biquartic/provenance.json (existenceStatus), data/rank-one-biquartic/why.md

import Definitions.Def_HodgeComputerRankOneBiquartic
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.RankOneBiquartic

theorem HodgeComputer.RankOneBiquartic.certificate_defect :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W) = F ^ 2 * Q := by sorry
