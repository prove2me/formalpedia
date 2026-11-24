-- Prove2me | Theorems.Thm_HodgeComputer_RankOneBiquartic_normalChart_degree_ten_witness
-- name    : HodgeComputer.RankOneBiquartic.normalChart_degree_ten_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:22:42.192747+00:00
-- url     : https://prove2.me/theorems/87e6b6a3-f6be-42df-a64b-8828a7658fde
-- title:
--   A normal-chart certificate at the canonical even denominator degree ten
-- statement:
--   Let $F$ be the rank-one biquartic sextic of the protected instance and $A$ its odd sextic source. There exist a denominator factor $S$ of degree ten, five numerator parameters $W_1,\dots,W_5$ of degree eleven and a quotient $Q$ such that $S\neq0$, $\gcd(S,F)=1$ and
--
--   $$\operatorname{defect}\bigl(F,A,D,1,N\bigr)=F^{2}Q,\qquad D=PS,\quad N_0=AS-\sum_{j\le5}(\partial_jF)W_j,\quad N_j=PW_j ,$$
--
--   where $P=\partial_0F$ and
--
--   $$\operatorname{defect}(F,A,D,q,N)=A D^2-qD\,N(F)+F\bigl(D\operatorname{div}(N)-N(D)\bigr).$$
--
--   This is the degree-ten instance of the certificate problem, stated in the cleared form of the key equation, with the pole parameter fixed at $q=1$. It differs from the unfixed statement only in that the degree of the denominator is required to be ten and the degrees of the numerator components are required to be eleven; conversely, a nonzero $S$ homogeneous of degree ten has total degree ten, so the unfixed statement follows from this one.
--
--   The existence statement is the open content of the certificate problem for this instance: the source records it as "not established by the cited methods", the mixed coupling $t=\tfrac57$ removes the product decomposition on which the split-case theorem relies, and the coefficient count at this degree is severely overdetermined, so the denominator has to be an exceptional one.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, section "One denominator and the normalized equations", equations (E1) and (E2); docs/05-computation.md, section 5.2 "Solving E1 does not solve E2"; data/rank-one-biquartic/instance.rec

import Definitions.Def_HodgeComputerRankOneBiquartic
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.RankOneBiquartic

theorem HodgeComputer.RankOneBiquartic.normalChart_degree_ten_witness :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous 11) ∧
      defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W) = F ^ 2 * Q := by sorry
