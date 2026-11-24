-- Prove2me | Theorems.Thm_HodgeComputer_RankOneBiquartic_normalChart_degree_ten_e2
-- name    : HodgeComputer.RankOneBiquartic.normalChart_degree_ten_e2
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:22:42.784667+00:00
-- url     : https://prove2.me/theorems/3d24f9b7-b96b-46d0-aff0-f0a6c95a1401
-- title:
--   The degree-ten normal chart satisfies the second normalized equation
-- statement:
--   Let $F$ be the rank-one biquartic sextic of the protected instance and $A$ its odd sextic source. We look for a denominator factor $S$ of degree ten and five numerator parameters $W_1,\dots,W_5$ of degree eleven, and require the second normalized equation $E_2$ of the certificate framework in the normal chart:
--
--   $$\operatorname{residue}_{F,A}(S,W)\in (F),\qquad\text{i.e.}\qquad \operatorname{residue}_{F,A}(S,W)=F\cdot Q .$$
--
--   Writing $P=\partial_0F$, $D=PS$ and
--
--   $$N_0=AS-\sum_{j=1}^{5}(\partial_jF)\,W_j,\qquad N_j=P\,W_j\quad(1\le j\le5),$$
--
--   the residue is
--
--   $$\operatorname{residue}_{F,A}(S,W)=D\cdot\operatorname{div}(N)-N(D),$$
--
--   so $E_2$ says that the rational vector field $N/D$ of the normal chart has its divergence defect supported on the hypersurface $V(F)$. Together with $S\neq0$, $\deg S=10$, $\gcd(S,F)=1$ and $\deg W_j=11$ this is the second half of the degree-ten normal-chart certificate; the first half, $E_1$, namely $\sum_i(\partial_iF)N_i=A\,D$, holds identically in the chart for every $S$ and every $W$, because $D=\partial_0F\,S$ is a partial derivative of $F$.
--
--   The existence statement is the open content. The source records the existence of a certificate for this target as "not established by the cited methods", and a direct coefficient count shows why the search must be done at an exceptional denominator: for a denominator of degree $e$ the equation is linear in the $5\binom{e+6}{5}$ coefficients of the $W_j$ against the coefficients of a residual of degree $2e+10$, which for $e=10$ gives $5\binom{16}{5}=21840$ unknowns against more than a million conditions in the quotient by $(F)$. The denominator $S$ itself must therefore be special, and this lemma asks for one that is both legal and effective at degree ten.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, section "One denominator and the normalized equations", equations (E1) and (E2); docs/05-computation.md, section 5.2 "Solving E1 does not solve E2"; data/rank-one-biquartic/instance.rec

import Definitions.Def_HodgeComputerRankOneBiquartic
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.RankOneBiquartic

theorem HodgeComputer.RankOneBiquartic.normalChart_degree_ten_e2 :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous 11) ∧
      NormalChart.residue F A S W = F * Q := by sorry
