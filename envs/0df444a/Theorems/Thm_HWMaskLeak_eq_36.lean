-- Prove2me | Theorems.Thm_HWMaskLeak_eq_36
-- name    : HWMaskLeak.eq_36
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T22:29:41.64779+00:00
-- url     : https://prove2.me/theorems/ec56170a-35c6-4e42-96f8-dd34df51fab8
-- title:
--   Eq. (36) — $|(1-\xi)\prod_{j<k}(1+\zeta\xi^{2^j})|\le2+2^{k+1}|1-\zeta|$
-- statement:
--   For unimodular complex numbers $\zeta,\xi$ and every integer $k\ge0$,
--   $$
--   \Bigl|(1-\xi)\prod_{j=0}^{k-1}\bigl(1+\zeta\xi^{2^j}\bigr)\Bigr|\le2+2^{k+1}|1-\zeta|.
--   $$
--
--   This telescoping-type bound controls the product of cosines along the doubling orbit in the proof of Claim C.2.
--
--   Differences from the source: none.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), proof of Claim C.2, p.48, eq. (36)

import Mathlib

namespace HWMaskLeak

/-- **Eq. (36)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), proof of Claim C.2, eq. (36), p.48): for unimodular `ζ, ξ` and `k ⩾ 0`,
`|(1 − ξ) Π_{j=0}^{k−1} (1 + ζ ξ^{2ʲ})| ⩽ 2 + 2^{k+1} |1 − ζ|`. -/
theorem eq_36 (ζ ξ : ℂ) (hζ : ‖ζ‖ = 1) (hξ : ‖ξ‖ = 1) (k : ℕ) :
    ‖(1 - ξ) * ∏ j ∈ Finset.range k, (1 + ζ * ξ ^ (2 ^ j))‖ ≤ 2 + 2 ^ (k + 1) * ‖1 - ζ‖ := by sorry

end HWMaskLeak
