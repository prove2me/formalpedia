-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_rate_zero_iff
-- name    : KWSpectrum.Estimator.rate_zero_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:28.053001+00:00
-- url     : https://prove2.me/theorems/34873c19-c617-4f20-a5ff-1983ba31dfa1
-- title:
--   p. 3 — the rate function is nonnegative on $\Sigma$ and vanishes only at $s = r$
-- statement:
--   Let $r, s \in \Sigma$ and let $I(s) = \sum_j s_j(\ln s_j - \ln r_j)$ be the rate function (13), with $0\ln 0 = 0$ and $I(s) = +\infty$ when $s_j > 0 = r_j$ for some $j$. Then
--   $$I(s) \ge 0, \qquad I(s) = 0 \iff s = r.$$
--
--   This is the property of the rate function that turns the large-deviation estimate into convergence to the true spectrum: every set at positive distance from $r$ has exponentially small probability.
--
--   Differences from the source: none.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 3 (sentence after eq. (11): "a positive function on Σ, called the rate function, which vanishes only for s = r") and eq. (13)

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 3 (after eq. (11)), with eq. (13): the rate
function is nonnegative on `Σ` and vanishes only at `s = r`. -/
theorem rate_zero_iff {d : ℕ} (r s : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    (hs : s ∈ SpectrumSet d) :
    0 ≤ rate r s ∧ (rate r s = 0 ↔ s = r) := by sorry

end KWSpectrum.Estimator
