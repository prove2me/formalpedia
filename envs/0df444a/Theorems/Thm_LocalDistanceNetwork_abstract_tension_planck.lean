-- Prove2me | Theorems.Thm_LocalDistanceNetwork_abstract_tension_planck
-- name    : LocalDistanceNetwork.abstract_tension_planck
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:32:26.36101+00:00
-- url     : https://prove2.me/theorems/afedef3d-3a9c-419c-ad18-25b3a6ba2024
-- title:
--   Abstract (6) — baseline $H_0$ is $7.1\sigma$ from Planck+$\Lambda$CDM
-- statement:
--   The tension between the baseline result $H_0=73.50\pm0.81\ \mathrm{km\,s^{-1}\,Mpc^{-1}}$ and the early-Universe plus $\Lambda$CDM value $67.24\pm0.35\ \mathrm{km\,s^{-1}\,Mpc^{-1}}$ rounds to $7.1\sigma$:
--   $$
--   7.05\le\frac{|73.50-67.24|}{\sqrt{0.81^{2}+0.35^{2}}}<7.15 .
--   $$
--
--   This checks the arithmetic behind the "$7.1\sigma$" figure in item (6) of the abstract.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Abstract (p. 1), Results items (2) and (6)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_Tension

namespace LocalDistanceNetwork
theorem abstract_tension_planck :
    (7.05 : ℝ) ≤ tensionSigma 73.50 0.81 67.24 0.35 ∧
    tensionSigma 73.50 0.81 67.24 0.35 < 7.15 := by sorry
end LocalDistanceNetwork
