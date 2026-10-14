-- Prove2me | Theorems.Thm_LocalDistanceNetwork_everything_tensions
-- name    : LocalDistanceNetwork.everything_tensions
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:33:43.496104+00:00
-- url     : https://prove2.me/theorems/d269f147-fa55-4edd-9345-eb27ed722d26
-- title:
--   Sect. 5.2.4 — V99 is $8.7\sigma$ and V99a is $8.1\sigma$ from Planck+$\Lambda$CDM
-- statement:
--   With the Table 4 values of the "everything available" solution V99 ($73.994\pm0.697$) and of V99A, everything except the Tully–Fisher relation ($73.656\pm0.713$), the tensions with the Planck+$\Lambda$CDM value $67.24\pm0.35$ (all in $\mathrm{km\,s^{-1}\,Mpc^{-1}}$) round to $8.7\sigma$ and $8.1\sigma$:
--   $$
--   8.65\le\frac{|73.994-67.24|}{\sqrt{0.697^{2}+0.35^{2}}}<8.75,\qquad
--   8.05\le\frac{|73.656-67.24|}{\sqrt{0.713^{2}+0.35^{2}}}<8.15 .
--   $$
--
--   This checks the arithmetic behind the "$8.7\sigma$" and "$8.1\sigma$" figures of Sect. 5.2.4.
--
--   **Formalization Note** The unrounded Table 4 values are used. With the rounded text values $73.99\pm0.70$ the V99 tension would be about $8.62\sigma$, which rounds to $8.6$ rather than the quoted $8.7$.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Sect. 5.2.4 (p. 17) and Table 4 (p. 9), rows V99 and V99A

import Mathlib
import Definitions.Def_LocalDistanceNetwork_Tension

namespace LocalDistanceNetwork
theorem everything_tensions :
    ((8.65 : ℝ) ≤ tensionSigma 73.994 0.697 67.24 0.35 ∧
      tensionSigma 73.994 0.697 67.24 0.35 < 8.75) ∧
    ((8.05 : ℝ) ≤ tensionSigma 73.656 0.713 67.24 0.35 ∧
      tensionSigma 73.656 0.713 67.24 0.35 < 8.15) := by sorry
end LocalDistanceNetwork
