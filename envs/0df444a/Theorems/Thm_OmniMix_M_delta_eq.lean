-- Prove2me | Theorems.Thm_OmniMix_M_delta_eq
-- name    : OmniMix.M_delta_eq
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:39:03.479858+00:00
-- url     : https://prove2.me/theorems/ebc7aae9-cb6c-4bec-8001-889cf50c9f65
-- title:
--   §3.2, p.13 — $M_\delta=\int_{I_\delta}[v(1-v)]^{-1}dv=2\log(2T+1)$
-- statement:
--   Let $T\in\mathbb N$ and $\delta=1/(2(T+1))$. Then
--   $$
--   \int_{\delta}^{1-\delta}\frac{dv}{v(1-v)}=2\log(2T+1).
--   $$
--
--   This is the normalizing constant of the threshold prior $\mu_\delta(dv)=dv/(M_\delta v(1-v))$ of Algorithm 2, and the source of the $\log T$ factor in its regret.
--
--   Differences from the source: none.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §3.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_OmniMix_Idelta
import Definitions.Def_OmniMix_deltaT

namespace OmniMix

/-- **Normalizing constant `M_δ` (§3.2, p.13).** Liu–Luo–Ratliff, arXiv:2610.41023, §3.2, p.13: "we restrict thresholds and
forecasts to `I_δ = [δ, 1 − δ]`, with a small `δ = 1/(2(T + 1))` … The density is then integrable, with
normalizing constant `M_δ = ∫_{I_δ}[v(1 − v)]⁻¹ dv = 2 log(2T + 1)`."

For every horizon `T ∈ ℕ` and `δ = 1/(2(T+1))`, `∫_{[δ,1−δ]} dv/(v(1−v)) = 2 log(2T+1)`.

**Formalization Note.** A Bochner integral over `I_δ` for Lebesgue measure. For `T ≥ 1` the right
side is positive, so the identity also asserts integrability; at `T = 0`, `I_δ = {1/2}` and both
sides are `0`. -/
theorem M_delta_eq (T : ℕ) :
    ∫ v in Idelta (deltaT T), 1 / (v * (1 - v)) = 2 * Real.log (2 * (T : ℝ) + 1) := by sorry

end OmniMix
