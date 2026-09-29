-- Prove2me | Theorems.Thm_Freiman_symbolic_lagrange_subset_markov
-- name    : Freiman.symbolic_lagrange_subset_markov
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:45.573465+00:00
-- url     : https://prove2.me/theorems/a23680eb-f20d-47fb-ae72-ced4dde74a89
-- title:
--   The symbolic Lagrange spectrum is contained in the symbolic Markov spectrum
-- statement:
--   Every finite symbolic Lagrange value is a finite symbolic Markov value. This is the inclusion in Theorem 1.3 which is separate from the existing server theorem stating equality of the classical and symbolic Lagrange spectra.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, printed p. 8.

import Definitions.Def_Freiman_symbolicMarkovSpectrum

namespace Freiman

theorem symbolic_lagrange_subset_markov :
    symbolicLagrangeSpectrum ⊆ symbolicMarkovSpectrum := by
  sorry

end Freiman
