-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_canonical_trace_primitive_exists
-- name    : HodgeComputer.SymmetricSexticResidual.canonical_trace_primitive_exists
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:44.78219+00:00
-- url     : https://prove2.me/theorems/2367d2bd-2d1d-4838-bc6c-51a5c3fef2f5
-- title:
--   Existence of a relative primitive for the linear canonical trace source of symmetric-sextic-residual
-- statement:
--   Let $f_{\mathrm{sym}}(\lambda, b, c, d, u) = \ell_{\mathrm{sym}} u^3 + B_{\mathrm{sym}} u^2 + C_{\mathrm{sym}} u + D_{\mathrm{sym}}$ be the reflection-chart cubic of `symmetric-sextic-residual`, and let $P_{\mathrm{lin}} = K_0 + K_1 u$ denote `symCanonicalSource`, where
--
--   $$
--   K_0 = 6 \ell_{\mathrm{sym}}^2 b d c^2 - 2 \ell_{\mathrm{sym}} C_{\mathrm{sym}} b d \lambda^2, \qquad K_1 = -6 \ell_{\mathrm{sym}}^2 b d (c^2 + \lambda^2) - 4 \ell_{\mathrm{sym}} B_{\mathrm{sym}} b d \lambda^2.
--   $$
--
--   The theorem asserts that $(f_{\mathrm{sym}}, K_0 + K_1 u)$ admits a cleared relative two-form primitive:
--
--   $$
--   \operatorname{RelativePrimitive}(f_{\mathrm{sym}},\; K_0 + K_1 u).
--   $$
--
--   Because $K_0 + K_1 u$ is strictly linear in the cubic fiber coordinate $u$, this isolates the normalized two-coefficient trace problem for `symmetric-sextic-residual`.
-- source:
--   Hodge.computer GitHub Discussion #117 (`fqlx`, `benediamond`, `kmehltretter82`), https://github.com/hodge-computer/sextics/discussions/117

import Definitions.Def_HodgeComputerSymmetricChart

theorem HodgeComputer.SymmetricSexticResidual.canonical_trace_primitive_exists :
    HodgeComputer.ReflectionChart.RelativePrimitive
      HodgeComputer.SymmetricSexticResidual.symWeighted
      HodgeComputer.SymmetricSexticResidual.symCanonicalSource := by sorry
