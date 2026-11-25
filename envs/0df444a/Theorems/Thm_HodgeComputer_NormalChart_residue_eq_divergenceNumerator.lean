-- Prove2me | Theorems.Thm_HodgeComputer_NormalChart_residue_eq_divergenceNumerator
-- name    : HodgeComputer.NormalChart.residue_eq_divergenceNumerator
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T10:35:30.304823+00:00
-- url     : https://prove2.me/theorems/62947c37-4006-4f23-bc17-d2fc4dd9d92d
-- title:
--   The normal-chart residue is the cleared divergence defect of the numerator
-- statement:
--   Let $R=\mathbb C[z_0,\ldots,z_5]$, let $F,A,S\in R$, and let $W=(W_1,\ldots,W_5)$ be five polynomials of $R$. Put $P=\partial_0F$ and $D=PS$, and let $N$ be the normal-chart numerator, whose components are
--
--   $$N_0=AS-\sum_{j=1}^{5}(\partial_jF)\,W_j,\qquad N_j=P\,W_j\quad(1\le j\le 5).$$
--
--   Then
--
--   $$\operatorname{residue}_{F,A}(S,W)=D\cdot\operatorname{div}(N)-N(D).$$
--
--   In other words the residue is exactly the cleared divergence defect of the rational vector field $N/D$ that the normal chart produces: it is the numerator of $\operatorname{div}(N/D)$ after clearing the denominator $D$.
--
--   The assertion is instance independent: it holds for every $F,A,S$ and every tuple $W$, so it is available to every normal-chart instance. Its content lies in the cancellation of the mixed partials of $F$ inside $\operatorname{div}(N)$. Because $\partial_0(\partial_jF)=\partial_j(\partial_0F)$, the two occurrences of $W_j$ in
--
--   $$\operatorname{div}(N)=\partial_0N_0+\sum_{j=1}^{5}\partial_jN_j$$
--
--   cancel pairwise, and one is left with
--
--   $$\operatorname{div}(N)=\partial_0A\,S+A\,\partial_0S+\sum_{j=1}^{5}\bigl(P\,\partial_jW_j-(\partial_jF)\,\partial_0W_j\bigr).$$
--
--   Substituting this together with $N(D)=(\partial_0D)N_0+\sum_{j\le5}(\partial_jD)N_j$ into $D\operatorname{div}(N)-N(D)$ and using $\partial_0D=S\partial_0P+P\partial_0S$ reproduces the defining formula for the residue.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, section "One denominator and the normalized equations", equations (E1) and (E2); data/rank-one-biquartic/instance.rec

import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.NormalChart MvPolynomial

theorem HodgeComputer.NormalChart.residue_eq_divergenceNumerator
    (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    residue F A S W = divergenceNumerator (denominator F S) (numerator F A S W) := by sorry
