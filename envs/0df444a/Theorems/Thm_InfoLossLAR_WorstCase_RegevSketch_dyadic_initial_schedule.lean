-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dyadic_initial_schedule
-- name    : InfoLossLAR.WorstCase.RegevSketch.dyadic_initial_schedule
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:26:19.626202+00:00
-- url     : https://prove2.me/theorems/329e7ff1-4dc9-4b46-b0f4-a586128d6354
-- title:
--   Bit-length bounded dyadic initialization and terminal DGS width
-- statement:
--   Let $n\ge1$, $q,\eta>0$, and let the initial width $W$ and requested width $r$ be positive rationals. Put $\sigma=n+2$ and suppose
--
--   $$
--   r\ge\frac{16q\sqrt n}{\sigma}\eta,\qquad
--   W\ge\frac{r\sigma}{\sqrt2\sqrt n}.
--   $$
--
--   Let $K$ be the sum of the binary lengths of the numerator of $W$ and the denominator of $r$. There is an integer $k\le K$ such that every source width $W/2^j$ for $0\le j\le k$ is strictly above $\sqrt2q\eta$, and the final source width $u=W/2^k$ permits terminal amplitude width $a=1/(\sqrt2r)$ inside the decoding radius:
--
--   $$
--   \sqrt n\,a\le \frac{\sigma}{2u},\qquad \frac{1}{\sqrt2 a}=r.
--   $$
--
--   The square of the threshold scale $r\sigma/(\sqrt2\sqrt n)$ is $r^2\sigma^2/(2n)$ and is rational. This gives a finite, bit-length bounded mathematical width plan from a sufficiently broad rational initial width to the exact requested terminal width, including the strict smoothing margin. It neither constructs the initial sampler and BDD oracle nor proves that the least crossing index or its comparison is implementable in the platform machine model.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.2, 3.3 and 3.14, pp. 18–19, 26–27. This is a separately derived fixed-family dyadic and bit-length parameter lemma for the exact terminal width; it is not a verbatim result or an algorithmic implementation in that source.

import Mathlib
set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSketch
theorem dyadic_initial_schedule (n : ℕ) (q eta : ℝ) (start target : ℚ)
    (hn : 0 < n) (hq : 0 < q) (heta : 0 < eta)
    (hstart : 0 < start) (htarget : 0 < target)
    (hthreshold : (16*q*Real.sqrt n/((n : ℝ)+2))*eta ≤ (target : ℝ))
    (hinit : (target : ℝ)*((n : ℝ)+2)/(Real.sqrt 2*Real.sqrt n) ≤ (start : ℝ)) :
    let K := Nat.size start.num.natAbs + Nat.size target.den
    ∃ k : ℕ, k ≤ K ∧
      (∀ j < k, Real.sqrt 2*q*eta < (start : ℝ)/(2 : ℝ)^j) ∧
      Real.sqrt 2*q*eta < (start : ℝ)/(2 : ℝ)^k ∧
      Real.sqrt n/(Real.sqrt 2*(target : ℝ)) ≤ ((n : ℝ)+2)/(2*((start : ℝ)/(2 : ℝ)^k)) ∧
      1/(Real.sqrt 2*(1/(Real.sqrt 2*(target : ℝ)))) = (target : ℝ) ∧
      ((target : ℝ)*((n : ℝ)+2)/(Real.sqrt 2*Real.sqrt n))^2 =
        (target : ℝ)^2*((n : ℝ)+2)^2/(2*(n : ℝ)) := by sorry
end InfoLossLAR.WorstCase.RegevSketch
