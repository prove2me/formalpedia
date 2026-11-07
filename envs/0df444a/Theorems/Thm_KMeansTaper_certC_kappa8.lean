-- Prove2me | Theorems.Thm_KMeansTaper_certC_kappa8
-- name    : KMeansTaper.certC_kappa8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:19.58766+00:00
-- url     : https://prove2.me/theorems/904a3eca-0b7d-4f86-abd0-36616ae1785e
-- title:
--   $[\mathrm C]$ at $\kappa=8$, $c=c_{0.85}$ (the certified statement of Section 6.2)
-- statement:
--   The certificate statement $[\mathrm C]$ holds for $\kappa=8$, $c=c_{0.85}$, $(\alpha_z,\gamma_z)=(2,6)$ and transfer thresholds $(\delta_H,\delta_{lo},\delta_{hi})=(0.375,0.5625,2)$: for every $x\in[0,1]$ and $w\in[0,1-x]$ there is $\alpha$ such that for every $D\ge0$ and $s\in\{0,1\}$ there is $\beta$ such that for all $q\in[0,1]$ and $Z\ge0$,
--
--   $$e_{D,s}(q,Z)-\Gamma(D;Z)+\Gamma(Z;D)\le\alpha(D-1)+\beta(Z-1).$$
--
--   This is what the interval-arithmetic certificate of Section 6.2 (268 cells, 3,655,983 leaf boxes, 1,837 of them delegated to Lemma 6.5) establishes through Proposition 6.4; with Theorem C.2 it gives Theorem 3.2.
--
--   Differences from the source:
--   - encoding: the certificate (cells, rows, boxes) passes the checks of Proposition 6.4, hence [C] holds → the statement [C] (CertC) for the constants of the κ = 8 run; reason: the certificate data are evidence for [C], not part of the mathematical statement
--   - encoding: c_{0.85}, 0.375, 0.5625 → the exact rationals c085, 3/8, 9/16; reason: same numbers
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 6.2, "Result", p.17 (PDF p.20); Proposition 6.4, p.14 (PDF p.17); constants (K1), p.13 (PDF p.16), and p.16 (PDF p.19)

import Mathlib
import Definitions.Def_KMeansTaper_c085
import Definitions.Def_KMeansTaper_CertC

namespace KMeansTaper

/-- **`[C]` at `κ = 8`, `c = c_{0.85}`** (the certified statement of Section 6.2, "Result",
p.17, PDF p.20; Proposition 6.4, p.14, PDF p.17).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

The certificate at `κ = 8` (constants `(α_z, γ_z) = (2, 6)` and transfer thresholds
`(δ_H, δ_lo, δ_hi) = (0.375, 0.5625, 2)` of (K1), p.13 and p.16), checked by verifier B with the
delegated boxes covered by Lemma 6.5, satisfies the hypotheses of Proposition 6.4, so `[C]` holds.

**Formalization Note.** The statement is `[C]` itself (Definition C.1) for these constants; the
certificate's boxes are not encoded. `c_{0.85}` is the exact rational `c085`. -/
theorem certC_kappa8 : CertC 8 (c085 : ℝ) 2 6 (3 / 8) (9 / 16) 2 := by sorry

end KMeansTaper
