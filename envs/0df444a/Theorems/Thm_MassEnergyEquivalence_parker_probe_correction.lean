-- Prove2me | Theorems.Thm_MassEnergyEquivalence_parker_probe_correction
-- name    : MassEnergyEquivalence.parker_probe_correction
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:17:32.88746+00:00
-- url     : https://prove2.me/theorems/6d48ca0d-9151-4b9a-aff2-86043f0982e7
-- title:
--   Parker Solar Probe: $\tfrac{3v^2}{4c^2} \approx 3.9\times10^{-8}$
-- statement:
--   For the Parker Solar Probe's 2018 speed $v = 68\,600\ \mathrm{m/s}$ and $c = 299\,792\,458\ \mathrm{m/s}$, the relative difference between the second- and third-order low-speed approximations of the energy satisfies
--
--   $$
--   \left|\frac{3v^2}{4c^2} - 3.9\times10^{-8}\right| < 5\times10^{-10},
--   $$
--
--   i.e. $\frac{3v^2}{4c^2}\approx 3.9\times10^{-8}$ to the two significant digits quoted in the article — an energy correction of about four parts per hundred million.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Low-speed approximation (p. 6): "The difference between the approximations for the Parker Solar Probe in 2018 is $\tfrac{3v^2}{4c^2} \approx 3.9\times10^{-8}$" with $v = 68{,}600$ m/s; $c = 299\,792\,458$ m/s from §Practical examples (p. 8).

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem parker_probe_correction :
    |3 * (68600 : ℝ) ^ 2 / (4 * (299792458 : ℝ) ^ 2) - 3.9e-8| < 0.05e-8 := by sorry

end MassEnergyEquivalence
