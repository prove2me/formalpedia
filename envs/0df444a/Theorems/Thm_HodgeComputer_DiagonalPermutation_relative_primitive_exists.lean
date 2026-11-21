-- Prove2me | Theorems.Thm_HodgeComputer_DiagonalPermutation_relative_primitive_exists
-- name    : HodgeComputer.DiagonalPermutation.relative_primitive_exists
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:58.12316+00:00
-- url     : https://prove2.me/theorems/be837ebc-df31-4066-b8c0-1a4fe0c68de2
-- title:
--   Existence of a cleared relative two-form primitive on the (01)-reflection cubic for diagonal-permutation
-- statement:
--   On the $(01)$-reflection chart $(1 + v, 1 - v, b, c + \lambda v, c - \lambda v, d)$ with $u = v^2$, let $f_{\mathrm{diag}}(\lambda, b, c, d, u) = \ell u^3 + B u^2 + C u + D$ be the weighted cubic of `diagonal-permutation` and let $P_{\mathrm{diag}}(\lambda, b, c, d, u)$ be the descended cubic source of $B_2 = X_0^3 Y_0^3 + X_1^3 Y_1^3 - 2 X_2^3 Y_2^3$.
--
--   The theorem asserts the existence of a cleared relative two-form primitive on $f_{\mathrm{diag}} = 0$:
--
--   $$
--   \operatorname{RelativePrimitive}(f_{\mathrm{diag}},\; P_{\mathrm{diag}}).
--   $$
--
--   Via reflection-chart transport and $S_3$-equivariant linear combination, this affine cubic primitive implies both `transposition_quotient_certificate` and the root target `HodgeComputer.DiagonalPermutation.certificate`.
-- source:
--   Hodge.computer Atlas instance `diagonal-permutation`, Chapter 3B and Discussion #177 (`benediamond`), https://github.com/hodge-computer/sextics/discussions/177

import Definitions.Def_HodgeComputerDiagonalPermutationQuotient

theorem HodgeComputer.DiagonalPermutation.relative_primitive_exists :
    HodgeComputer.ReflectionChart.RelativePrimitive
      HodgeComputer.DiagonalPermutation.diagWeighted
      HodgeComputer.DiagonalPermutation.diagSource := by sorry
