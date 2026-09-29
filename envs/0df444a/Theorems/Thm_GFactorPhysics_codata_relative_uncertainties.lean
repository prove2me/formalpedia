-- Prove2me | Theorems.Thm_GFactorPhysics_codata_relative_uncertainties
-- name    : GFactorPhysics.codata_relative_uncertainties
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:49:51.031623+00:00
-- url     : https://prove2.me/theorems/7a9f6796-91a6-490e-bbfb-f70e0e770d27
-- title:
--   CODATA g-factor table: relative standard uncertainties
-- statement:
--   The article's table of CODATA recommended g-factor values lists, for each particle, a value with its standard uncertainty in the last two digits, and a relative standard uncertainty. Writing $u$ for the standard uncertainty and $|g|$ for the absolute value of the g-factor, the printed relative uncertainties are the two-significant-digit roundings of $u/|g|$:
--
--   1. electron, $g_e=-2.002\,319\,304\,360\,92(36)$: $\;1.75\times10^{-13}\le \dfrac{3.6\times10^{-13}}{|g_e|} < 1.85\times10^{-13}$, i.e. $1.8\times10^{-13}$;
--   2. muon, $g_\mu=-2.002\,331\,841\,23(82)$: $\;4.05\times10^{-10}\le \dfrac{8.2\times10^{-10}}{|g_\mu|} < 4.15\times10^{-10}$, i.e. $4.1\times10^{-10}$;
--   3. proton, $g_p=+5.585\,694\,6893(16)$: $\;2.85\times10^{-10}\le \dfrac{1.6\times10^{-9}}{|g_p|} < 2.95\times10^{-10}$, i.e. $2.9\times10^{-10}$;
--   4. neutron, $g_n=-3.826\,085\,52(90)$: $\;2.35\times10^{-7}\le \dfrac{9.0\times10^{-7}}{|g_n|} < 2.45\times10^{-7}$, i.e. $2.4\times10^{-7}$.
--
--   This checks the internal consistency of the article's table.
-- source:
--   Wikipedia, "g-factor (physics)" (PDF snapshot supplied by the user, `G-factor_(physics).pdf`), https://en.wikipedia.org/wiki/G-factor_(physics); section "Recommended g-factor values", table "CODATA recommended g-factor values".

import Mathlib

namespace GFactorPhysics
theorem codata_relative_uncertainties :
    ((1.75e-13 : ℝ) ≤ (3.6e-13 : ℝ) / |(-2.00231930436092 : ℝ)| ∧
      (3.6e-13 : ℝ) / |(-2.00231930436092 : ℝ)| < 1.85e-13) ∧
    ((4.05e-10 : ℝ) ≤ (8.2e-10 : ℝ) / |(-2.00233184123 : ℝ)| ∧
      (8.2e-10 : ℝ) / |(-2.00233184123 : ℝ)| < 4.15e-10) ∧
    ((2.85e-10 : ℝ) ≤ (1.6e-9 : ℝ) / |(5.5856946893 : ℝ)| ∧
      (1.6e-9 : ℝ) / |(5.5856946893 : ℝ)| < 2.95e-10) ∧
    ((2.35e-7 : ℝ) ≤ (9.0e-7 : ℝ) / |(-3.82608552 : ℝ)| ∧
      (9.0e-7 : ℝ) / |(-3.82608552 : ℝ)| < 2.45e-7) := by sorry
end GFactorPhysics
