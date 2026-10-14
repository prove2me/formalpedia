-- Prove2me | Theorems.Thm_LocalDistanceNetwork_abstract_tension_desi
-- name    : LocalDistanceNetwork.abstract_tension_desi
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:32:51.668582+00:00
-- url     : https://prove2.me/theorems/edf35cab-0d70-489d-a01d-b7b0ca76b6f4
-- title:
--   Abstract (6) — baseline $H_0$ is $5.0\sigma$ from BBN+BAO (DESI DR2)
-- statement:
--   The tension between the baseline result $H_0=73.50\pm0.81\ \mathrm{km\,s^{-1}\,Mpc^{-1}}$ and the BBN+BAO value within flat $\Lambda$CDM from DESI DR2, $68.51\pm0.58\ \mathrm{km\,s^{-1}\,Mpc^{-1}}$, rounds to $5.0\sigma$:
--   $$
--   4.95\le\frac{|73.50-68.51|}{\sqrt{0.81^{2}+0.58^{2}}}<5.05 .
--   $$
--
--   This checks the arithmetic behind the "$5.0\sigma$" figure in item (6) of the abstract.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Abstract (p. 1), Results items (2) and (6)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_Tension

namespace LocalDistanceNetwork
theorem abstract_tension_desi :
    (4.95 : ℝ) ≤ tensionSigma 73.50 0.81 68.51 0.58 ∧
    tensionSigma 73.50 0.81 68.51 0.58 < 5.05 := by sorry
end LocalDistanceNetwork
