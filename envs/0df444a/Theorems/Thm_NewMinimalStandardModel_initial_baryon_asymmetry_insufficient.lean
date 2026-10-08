-- Prove2me | Theorems.Thm_NewMinimalStandardModel_initial_baryon_asymmetry_insufficient
-- name    : NewMinimalStandardModel.initial_baryon_asymmetry_insufficient
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T13:39:44.605635+00:00
-- url     : https://prove2.me/theorems/f2c6bd20-62d1-48b6-bd0b-78eb6e4dfd5c
-- title:
--   A pre-inflationary baryon asymmetry is diluted below $10^{-18}$
-- statement:
--   Let $N$ be the number of e-folds of inflation, with $N \ge \ln(10\,\mathrm{Gpc}/10\,\mathrm{kpc}) = \ln 10^6$. Let $\mu_F>0$ be the Fermi momentum of a pre-inflationary Fermi-degenerate baryon gas and $\rho_\varphi>0$ the inflaton energy density, and suppose the dilution relation
--   $$\frac{\mu_F^4}{\rho_\varphi} = e^{-4N}$$
--   holds at the end of inflation. Then the maximal baryon asymmetry after instantaneous reheating satisfies
--   $$\eta \simeq \frac{\mu_F^3}{\rho_\varphi^{3/4}} \le 10^{-18} \qquad\text{and}\qquad \frac{\mu_F^3}{\rho_\varphi^{3/4}} < 8.8\times 10^{-11},$$
--   the latter being the lower end of the observed value $\eta = 9.2^{+0.6}_{-0.4}\times10^{-11}$ quoted on p. 118. Hence the observed asymmetry cannot be an initial condition once inflation is accepted.
-- source:
--   H. Davoudiasl, R. Kitano, T. Li, H. Murayama, The new Minimal Standard Model, Phys. Lett. B 609 (2005) 117-123, https://doi.org/10.1016/j.physletb.2005.01.026, p. 120, right column (argument that baryogenesis is necessary)

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

namespace NewMinimalStandardModel

theorem initial_baryon_asymmetry_insufficient (N μF ρφ : ℝ)
    (hN : Real.log ((10 * 10 ^ 9 : ℝ) / (10 * 10 ^ 3)) ≤ N)
    (hμ : 0 < μF) (hρ : 0 < ρφ) (hdil : μF ^ 4 / ρφ = Real.exp (-4 * N)) :
    μF ^ 3 / ρφ ^ ((3 : ℝ) / 4) ≤ (10 : ℝ) ^ (-18 : ℤ) ∧
      μF ^ 3 / ρφ ^ ((3 : ℝ) / 4) < 88 / 10 ^ 12 := by sorry

end NewMinimalStandardModel
