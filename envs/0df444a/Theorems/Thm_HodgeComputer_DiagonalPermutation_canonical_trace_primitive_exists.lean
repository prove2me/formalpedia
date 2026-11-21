-- Prove2me | Theorems.Thm_HodgeComputer_DiagonalPermutation_canonical_trace_primitive_exists
-- name    : HodgeComputer.DiagonalPermutation.canonical_trace_primitive_exists
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:56.233173+00:00
-- url     : https://prove2.me/theorems/13825172-87ae-4f8e-9f1d-052f8c828089
-- title:
--   Existence of a relative primitive for the linear canonical trace source of diagonal-permutation
-- statement:
--   Let $f_{\mathrm{diag}}(\lambda, b, c, d, u) = \ell u^3 + B u^2 + C u + D$ be the $(01)$-reflection cubic of `diagonal-permutation`, where $\ell(\lambda) = 2 + \frac{10}{7}\lambda^2 + 2\lambda^6$, and let $K_0 + K_1 u$ denote the cleared linear-in-$u$ canonical trace source `diagCanonicalSource` built from the cubic source $P_{\mathrm{diag}} = p_0 + p_1 u + p_2 u^2 + p_3 u^3$ via
--
--   $$
--   K_0 = 6 \ell^2 p_0 - 2 \ell C p_2 + (3 \ell D + B C) p_3, \qquad K_1 = 6 \ell^2 p_1 - 4 \ell B p_2 + 2 B^2 p_3.
--   $$
--
--   The theorem asserts that $(f_{\mathrm{diag}}, K_0 + K_1 u)$ admits a cleared relative primitive on $f_{\mathrm{diag}} = 0$:
--
--   $$
--   \operatorname{RelativePrimitive}(f_{\mathrm{diag}},\; K_0 + K_1 u).
--   $$
--
--   Although $P_{\mathrm{diag}}$ has degree $3$ in $u$ ($p_3 = 2\lambda^3 \neq 0$), cancelling its pole and quadratic branch trace reduces `diagonal-permutation` to the same linear-in-$u$ relative-primitive shape as `symmetric-sextic-residual`.
-- source:
--   Hodge.computer Atlas instance `diagonal-permutation` and Discussion #177, https://github.com/hodge-computer/sextics/discussions/177

import Definitions.Def_HodgeComputerDiagonalPermutationQuotient

theorem HodgeComputer.DiagonalPermutation.canonical_trace_primitive_exists :
    HodgeComputer.ReflectionChart.RelativePrimitive
      HodgeComputer.DiagonalPermutation.diagWeighted
      HodgeComputer.DiagonalPermutation.diagCanonicalSource := by sorry
