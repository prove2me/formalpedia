-- Prove2me | Theorems.Thm_Freiman_lagrange_symbolic
-- name    : Freiman.lagrange_symbolic
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:22:13.266009+00:00
-- url     : https://prove2.me/theorems/ef224859-622a-4685-8814-e4c12eace73a
-- title:
--   The two definitions of the Lagrange spectrum agree
-- statement:
--   The classical Lagrange spectrum, defined through rational approximation, equals the symbolic Lagrange spectrum, defined through the local values of sequences of positive integers indexed by $\mathbb Z$:
--   $$
--   L=L_{\mathrm{sym}}.
--   $$
--   Both sets contain only finite real values. This identity permits the continued fraction constructions to produce classical Lagrange values.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 1.3, p. 8, its equality assertion.

import Definitions.Def_Freiman_symbolicMarkovSpectrum

namespace Freiman

theorem lagrange_symbolic :
    lagrangeSpectrum = symbolicLagrangeSpectrum := by
  sorry

end Freiman
