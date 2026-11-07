-- Prove2me | Theorems.Thm_HWMaskLeak_eq_5
-- name    : HWMaskLeak.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:38.933786+00:00
-- url     : https://prove2.me/theorems/b9533482-5b55-4e2e-858f-7d7d2092eaa3
-- title:
--   Eq. (5) — generating function of $N\hat B_w(t)$
-- statement:
--   For every $n$, every $N\ge1$, every $t\in\mathbb Z/N\mathbb Z$ and every $w\ge0$,
--   $$
--   N\,\hat B_w(t)=[z^w]\prod_{j=0}^{n-1}\bigl(1+z\,e_N(-2^jt)\bigr),
--   $$
--   where $[z^w]$ takes the coefficient of $z^w$ of the polynomial in $z$.
--
--   Because the full-range model keeps all $n$ binary coordinates, the unnormalized Fourier sum over a weight layer is a coefficient of a product, which opens the way to the Cauchy-integral estimates.
--
--   Differences from the source:
--   - generalization: N near 2ⁿ (the setting of §1.3.1 and §4), weights w ∈ W_bin → every n, every N ≥ 1, every w ∈ ℕ; reason: the identity is the expansion of the product over all n-bit strings and holds for every N; for w > n both sides are 0
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §1.3.1, p.11, eq. (5); derived in §2.2, p.16

import Mathlib
import Definitions.Def_HWMaskLeak_fullRange

namespace HWMaskLeak

open Polynomial

/-- **Eq. (5), the generating function of `B̂_w`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), §1.3.1, eq. (5), p.11; derived in §2.2,
p.16): `N B̂_w(t) = [z^w] Π_{j=0}^{n−1} (1 + z · e_N(−2ʲt))`.

**Formalization Note** `z` is the indeterminate of `ℂ[X]` and `[z^w]` is `Polynomial.coeff w`;
`e_N(−2ʲt)` is `ZMod.stdAddChar (−(2ʲ t))`. Stated for every `n`, `N ⩾ 1`, `t` and `w ∈ ℕ`. -/
theorem eq_5 (n N : ℕ) [NeZero N] (w : ℕ) (t : ZMod N) :
    (N : ℂ) * fullRangeHat n N w t =
      (∏ j ∈ Finset.range n, (1 + X * C (ZMod.stdAddChar (-((2 : ZMod N) ^ j * t))))).coeff w := by sorry

end HWMaskLeak
