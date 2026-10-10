-- Prove2me | Theorems.Thm_MassEnergyEquivalence_rest_energy_one_kilogram
-- name    : MassEnergyEquivalence.rest_energy_one_kilogram
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:17:52.501503+00:00
-- url     : https://prove2.me/theorems/fb58fe73-ce45-425e-ab9b-64979c978043
-- title:
--   Energy equivalent of one kilogram: $c^2 = 89\,875\,517\,873\,681\,764$ J/kg
-- statement:
--   In SI units, with $c = 299\,792\,458\ \mathrm{m/s}$, the rest energy of a mass of one kilogram is
--
--   $$
--   E = (1\ \mathrm{kg})\,c^2 = 89\,875\,517\,873\,681\,764\ \mathrm J \;(\approx 9.0\times10^{16}\ \mathrm J \approx 89.9\ \mathrm{PJ}).
--   $$
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Practical examples (pp. 7–8): "$E/m = c^2 = (299\,792\,458$ m/s$)^2 = 89\,875\,517\,873\,681\,764$ J/kg"; "the energy equivalent of one kilogram of mass is 89.9 petajoules".

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem rest_energy_one_kilogram :
    restEnergy 299792458 1 = 89875517873681764 := by sorry

end MassEnergyEquivalence
