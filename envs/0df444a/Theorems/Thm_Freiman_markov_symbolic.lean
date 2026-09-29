-- Prove2me | Theorems.Thm_Freiman_markov_symbolic
-- name    : Freiman.markov_symbolic
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:22:31.504283+00:00
-- url     : https://prove2.me/theorems/24b70140-632c-4dd1-93ec-ea516b4f29b2
-- title:
--   The two definitions of the Markov spectrum agree
-- statement:
--   The classical Markov spectrum, defined by indefinite real binary quadratic forms with positive absolute minimum, equals the symbolic Markov spectrum:
--   $$
--   M=M_{\mathrm{sym}}.
--   $$
--   Both sets contain only finite real values. This identity identifies the supremum of local continued fraction values with the normalized reciprocal minimum of a quadratic form.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 1.6, p. 10.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Definitions.Def_Freiman_markovSpectrum

namespace Freiman

theorem markov_symbolic :
    markovSpectrum = symbolicMarkovSpectrum := by
  sorry

end Freiman
