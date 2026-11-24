-- Prove2me | Theorems.Thm_HodgeComputer_NormalChart_directional_eq_source
-- name    : HodgeComputer.NormalChart.directional_eq_source
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T10:35:28.033216+00:00
-- url     : https://prove2.me/theorems/e57783ee-0500-4c84-a5cd-f3088eda127a
-- title:
--   The normal-chart numerator satisfies the first normalized equation identically
-- statement:
--   With the notation of the normal chart — $P=\partial_0F$, $D=PS$, $N_0=AS-\sum_{j=1}^{5}(\partial_jF)W_j$ and $N_j=PW_j$ for $1\le j\le5$ — one has for all $F,A,S$ and all $W$
--
--   $$N(F)=\sum_{i=0}^{5}(\partial_iF)\,N_i=A\cdot D.$$
--
--   This is the first normalized equation of the certificate framework, $E_1$, and in the normal chart it holds identically: no choice of the numerator $W$ is needed to achieve it, because the two appearances of $W_j$ in $N(F)$ cancel between the terms $\partial_0F\cdot N_0$ and $\partial_jF\cdot N_j$,
--
--   $$\partial_0F\cdot N_0+\partial_jF\cdot N_j=P\bigl(AS-\textstyle\sum_{k}(\partial_kF)W_k\bigr)+\partial_jF\cdot P\,W_j=P\,AS.$$
--
--   So the whole freedom of the numerator is visible in the second normalized equation $E_2$, namely $D\operatorname{div}(N)-N(D)\in(F^q)$, and the present statement isolates that freedom. The assertion is instance independent and holds for every $F,A,S,W$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, section "One denominator and the normalized equations", equations (E1) and (E2); data/rank-one-biquartic/instance.rec

import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.NormalChart MvPolynomial

theorem HodgeComputer.NormalChart.directional_eq_source
    (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    directional F (numerator F A S W) = A * (denominator F S) := by sorry
