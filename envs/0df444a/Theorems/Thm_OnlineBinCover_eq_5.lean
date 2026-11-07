-- Prove2me | Theorems.Thm_OnlineBinCover_eq_5
-- name    : OnlineBinCover.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:57.750662+00:00
-- url     : https://prove2.me/theorems/a98abd94-3481-4c0f-b4ef-10f467567191
-- title:
--   (5) — $\mathrm{OPT}(I)\le\mathrm{vol}(I)<2\mathrm{OPT}(I)+1$
-- statement:
--   For every instance $I$ of $n$ items with sizes in $(0,1]$,
--
--   $$\mathrm{OPT}(I)\le\mathrm{vol}(I)<2\,\mathrm{OPT}(I)+1.$$
--
--   The first inequality holds because every covered bin has load at least $1$; the second because Dual Next-Fit leaves covered bins of load below $2$ and one unfinished bin of load below $1$. The bounds convert between volume and optimum throughout the analysis.
--
--   Differences from the source: none.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), (5), App. B, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_OnlineBinCover_Basic

namespace OnlineBinCover

/-- (5), App. B, p.18. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

`OPT(I) ≤ vol(I) < 2 OPT(I) + 1` for every instance with sizes in `(0, 1]`. -/
theorem eq_5 {n : ℕ} (s : Fin n → ℝ) (hs : ValidSizes s) :
    (OPT s : ℝ) ≤ vol s ∧ vol s < 2 * (OPT s : ℝ) + 1 := by sorry

end OnlineBinCover
