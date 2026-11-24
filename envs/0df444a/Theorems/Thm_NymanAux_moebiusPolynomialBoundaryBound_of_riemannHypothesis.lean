-- Prove2me | Theorems.Thm_NymanAux_moebiusPolynomialBoundaryBound_of_riemannHypothesis
-- name    : NymanAux.moebiusPolynomialBoundaryBound_of_riemannHypothesis
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T01:50:27.630059+00:00
-- url     : https://prove2.me/theorems/f6432081-7a5c-4c94-bbfd-fe0b42e431d0
-- title:
--   Under RH, Möbius Dirichlet polynomials are $O(|t|^\beta)$ uniformly in length on $\operatorname{Re}s>\tfrac12+\eta$
-- statement:
--   Assume the Riemann hypothesis. For every $\eta>0$ and $\beta>0$ there is a constant $C\ge0$ such that for every $N\ge0$ and every $s=\sigma+it$ with $\sigma>\tfrac12+\eta$,
--   $$\Bigl|\sum_{d=1}^{N}\frac{\mu(d)}{d^{s}}\Bigr|\le C\,(1+|t|)^{\beta}.$$
--   The bound is uniform in the length $N$ of the Dirichlet polynomial. This is the hypothesis `NymanBeurling.MoebiusPolynomialBoundaryBound` of the proved completion theorem `NymanBeurling.damped_mellin_completion_of_polynomial_bound`.
-- source:
--   Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., §14.25 (Perron's formula with the RH bound $1/\zeta(s)\ll|t|^{\varepsilon}$ for $\sigma\ge\tfrac12+\delta$); used in Broughan, Equivalents of the Riemann Hypothesis, Vol. II, §3.4.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_NymanBeurling_DampedMellinFrontiers

theorem NymanAux.moebiusPolynomialBoundaryBound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    NymanBeurling.MoebiusPolynomialBoundaryBound := by sorry
