-- Prove2me | Theorems.Thm_LogLogJam_Supplement_squeezing_from_photon_mean
-- name    : LogLogJam.Supplement.squeezing_from_photon_mean
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:10.601865+00:00
-- url     : https://prove2.me/theorems/d16cddd0-fbae-5da6-9e4a-e2a8e9784022
-- title:
--   Converting photon-number mean error to squeezing error
-- statement:
--   Let $r\geq0$ denote the input squeezing and let $\mu\geq0$ estimate the mean photon count. If $0\leq\eta\leq 1/4$ and $|\mu-\sinh^2r|\leq\eta\cosh(r)\sinh(r)$, the reconstructed squeezing $\operatorname{arsinh}\sqrt\mu$ differs from $r$ by at most $4\eta$, including at vacuum.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — §8.3.3, Lemma 8.27, Eq. (170)

import Mathlib

namespace LogLogJam.Supplement

theorem squeezing_from_photon_mean {r μ η : ℝ} (hr : 0 ≤ r) (hμ : 0 ≤ μ)
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (h : |μ - Real.sinh r ^ 2| ≤ η * Real.cosh r * Real.sinh r) :
    |Real.arsinh (Real.sqrt μ) - r| ≤ 4 * η := by sorry

end LogLogJam.Supplement
