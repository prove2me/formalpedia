-- Prove2me | Theorems.Thm_KMeansTaper_theorem_C_2
-- name    : KMeansTaper.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:08.085199+00:00
-- url     : https://prove2.me/theorems/dfa06914-f3b8-4bbd-9f12-44ecac1eed9e
-- title:
--   Theorem C.2 — $[\mathrm C]$ implies $\mathrm{SFI}(\kappa,c)$
-- statement:
--   Let $\kappa\ge8$, $0<c\le1$, $\alpha_z,\gamma_z\ge0$ with $\alpha_z+\gamma_z\le\kappa$, and thresholds $0<\delta_H<\delta_{lo}<\delta_{hi}$. If the certificate statement $[\mathrm C]$ holds for these constants, then $\mathrm{SFI}(\kappa,c)$ holds.
--
--   This reduces SFI, an inequality over all finite configurations, to the five-variable pointwise statement $[\mathrm C]$ that a computer can certify.
--
--   Differences from the source:
--   - generalization: dyadic thresholds 0 < δ_H < δ_lo < δ_hi → real thresholds 0 < δ_H < δ_lo < δ_hi; reason: the proof uses only the antisymmetry of the transfer terms; dyadic thresholds are a special case
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem C.2 and Definition C.1, p.32 (PDF p.35); per-column excess and standing assumptions of Appendix C, p.31 (PDF p.34)

import Mathlib
import Definitions.Def_KMeansTaper_SFI
import Definitions.Def_KMeansTaper_CertC

namespace KMeansTaper

/-- **Theorem C.2 (`[C]` implies `SFI(κ, c)`)**, p.32 (PDF p.35), with Definition C.1 and the
per-column excess of p.31 (PDF p.34).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Throughout Appendix C, `κ ≥ 8` and `c ∈ (0, 1]` are fixed, `η = κ - 8 ≥ 0`, and
`α_z, γ_z ≥ 0` satisfy `α_z + γ_z ≤ κ`. Fix thresholds `0 < δ_H < δ_lo < δ_hi`. Then `[C]`
implies `SFI(κ, c)`.

**Formalization Note.** The thresholds are real numbers; the paper fixes dyadic ones. -/
theorem theorem_C_2 (κ c αz γz δH δlo δhi : ℝ) (hκ : 8 ≤ κ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hαz : 0 ≤ αz) (hγz : 0 ≤ γz) (hsum : αz + γz ≤ κ) (hH : 0 < δH) (hHlo : δH < δlo)
    (hlohi : δlo < δhi) (hC : CertC κ c αz γz δH δlo δhi) : SFI κ c := by sorry

end KMeansTaper
