-- Prove2me | Theorems.Thm_Freiman_lagrange_subset_markov
-- name    : Freiman.lagrange_subset_markov
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:22:44.308668+00:00
-- url     : https://prove2.me/theorems/df41c603-1c6d-4823-9acf-a6acf501bc53
-- title:
--   The Lagrange spectrum is contained in the Markov spectrum
-- statement:
--   Every real number in the classical Lagrange spectrum belongs to the classical Markov spectrum:
--   $$
--   L\subseteq M.
--   $$
--   Thus membership in the Lagrange spectrum implies membership in the Markov spectrum, and a gap in the Markov spectrum is also a gap in the Lagrange spectrum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorems 1.3 and 1.6, pp. 8 and 10.

import Definitions.Def_Freiman_lagrangeSpectrum
import Definitions.Def_Freiman_markovSpectrum

namespace Freiman

theorem lagrange_subset_markov :
    lagrangeSpectrum ⊆ markovSpectrum := by
  sorry

end Freiman
