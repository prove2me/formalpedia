-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_parameter_bounds
-- name    : ITPIRPreproc.MatchVec.polynomial_parameter_bounds
-- status  : Proved
-- author  : @Jesko
-- created : 2026-11-13T17:21:57.031886+00:00
-- url     : https://prove2.me/theorems/abd15bea-35f7-4f94-abc6-abfde93744e8
-- title:
--   Appendix A — explicit subpolynomial dimension bound
-- statement:
--   Let $h\ge3$, let $\ell$ be the least natural number satisfying $\ell^\ell\ge2^h$, and let $2^a$ and $3^b$ be the least powers of $2$ and $3$ strictly exceeding $\sqrt\ell$. Put $k=\max(2^a,3^b)-1$. For any bijective enumeration by $[d]$ of the coordinates $(I,\alpha)$ in the polynomial construction,
--   $$\ell^\ell\ge2^h,\qquad k\ge1,\qquad\ell<2^a3^b,\qquad d\le2^{1000\sqrt{h\ln h}}.$$
--   The constant 1000 is a convenient absolute constant, not an optimized value. This makes the asymptotic dimension claim in Appendix A explicit for all $h\ge3$. It is a dimension and parameter theorem; it makes no RAM implementation claim.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Appendix A, printed pp.36-37 (PDF pp.38-39), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/572.pdf

import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters
open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction

theorem ITPIRPreproc.MatchVec.polynomial_parameter_bounds (h d : ℕ) (hh : 3 ≤ h)
    (coords : Fin d ≃ Coordinate (wordLength h) (degree (exponent2 h) (exponent3 h))) :
    2^h ≤ (wordLength h)^(wordLength h) ∧
    1 ≤ degree (exponent2 h) (exponent3 h) ∧
    wordLength h < 2^(exponent2 h) * 3^(exponent3 h) ∧
    (d:ℝ) ≤ (2:ℝ)^(1000 * Real.sqrt ((h:ℝ)*Real.log h)) := by sorry
