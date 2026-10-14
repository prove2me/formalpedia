-- Prove2me | Theorems.Thm_LocalDistanceNetwork_abstract_relative_uncertainty
-- name    : LocalDistanceNetwork.abstract_relative_uncertainty
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:31:56.459028+00:00
-- url     : https://prove2.me/theorems/eb6da2a4-d734-4edf-8d7f-f9f89af581ad
-- title:
--   Abstract (2) — relative uncertainty $1.1\%$ (baseline) and $0.9\%$ (all estimators)
-- statement:
--   Using the values of Table 4 of the paper, the baseline solution V00 ($H_0=73.499\pm0.809\ \mathrm{km\,s^{-1}\,Mpc^{-1}}$) and the "everything available" solution V99 ($H_0=73.994\pm0.697\ \mathrm{km\,s^{-1}\,Mpc^{-1}}$) have relative uncertainties that round to $1.1\%$ and $0.9\%$ respectively:
--   $$
--   1.05\%\le\frac{0.809}{73.499}<1.15\%,\qquad 0.85\%\le\frac{0.697}{73.994}<0.95\%.
--   $$
--
--   This checks the arithmetic behind item (2) of the abstract: "A covariance-weighted combination yields a relative uncertainty of 1.1% (baseline) or 0.9% (all estimators)".
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Abstract (p. 1), Results items (2) and (6)

import Mathlib

namespace LocalDistanceNetwork
theorem abstract_relative_uncertainty :
    (0.0105 : ℝ) ≤ 0.809 / 73.499 ∧ (0.809 : ℝ) / 73.499 < 0.0115 ∧
    (0.0085 : ℝ) ≤ 0.697 / 73.994 ∧ (0.697 : ℝ) / 73.994 < 0.0095 := by sorry
end LocalDistanceNetwork
