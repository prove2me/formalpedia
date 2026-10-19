-- Prove2me | Theorems.Thm_GoodmanWitten_eq1_counting_rate
-- name    : GoodmanWitten.eq1_counting_rate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:52:36.578618+00:00
-- url     : https://prove2.me/theorems/87621ad9-8a7f-45a1-af2f-59e8dc3d33b5
-- title:
--   Eq. (1): counting rate per kilogram of detector per day
-- statement:
--   Let a detector consist of nuclei of mass number $A>0$, with $K = 6.0\times10^{26}/A$ nuclei per kilogram, and let halo particles of mass $m>0$ (GeV), mass density $\rho$ (g/cm$^3$) and mean velocity $v$ (cm/s) have flux $F = \rho v/m$ and cross section $\sigma$ (cm$^2$). Write $R = KF\sigma$ in events per kg per day and $\bar\sigma = (\sigma/A)(1\ \mathrm{GeV}/m)$. Then there is a constant $C$ with $|C/5.8 - 1| \le 0.05$ such that, for all such parameters,
--   $$
--   R = C\left[\frac{\bar\sigma}{10^{-38}\ \mathrm{cm}^2}\right]\left[\frac{\rho}{10^{-24}\ \mathrm{g/cm}^3}\right]\left[\frac{v}{200\ \mathrm{km/s}}\right].
--   $$
--
--   This is the master formula all three classes of dark-matter candidates are fed into.
--
--   **Formalization Note** The paper prints the coefficient to two significant figures; agreement within 5% relative error is required.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3060, Eq. (1) and the definition of sigma-bar below it

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem eq1_counting_rate : ∃ C : ℝ, |C / 5.8 - 1| ≤ 0.05 ∧
    ∀ A σ ρ v m : ℝ, 0 < A → 0 < m →
      eventRatePerKgDay A σ ρ v m =
        C * (reducedCrossSection A σ m / 1e-38) * (ρ / 1e-24) * (v / 2e7) := by sorry

end GoodmanWitten
