-- Prove2me | Theorems.Thm_KhintchineTwoRegime_sixProfile_endpoint
-- name    : KhintchineTwoRegime.sixProfile_endpoint
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:12.060846+00:00
-- url     : https://prove2.me/theorems/09437fa0-dcca-4258-b6c6-533a73936645
-- title:
--   Matching of the four- and six-coordinate profiles at $d_0$
-- statement:
--   At $d_0=\sqrt{2-\sqrt2}$ and in every dimension $n\ge4$, the four- and six-coordinate profiles coincide:
--   $$
--   \omega^{(6)}_{d_0}=\omega_{d_0}=(1/2,1/2,1/2,1/2,0,\ldots,0).
--   $$
--   Moreover, with $q=(2-d_0^2)/\sqrt2=1$, their common moment formulas agree:
--   $$
--   A(q)=\frac1{\sqrt2}+\left(\sqrt{1-\frac{d_0^2}{4}}-d_0\right)\frac{d_0}{2\sqrt2}=\frac34.
--   $$
--
--   This identifies the endpoint of the six-coordinate regime with the sharp four-coordinate profile of Theorem 1.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Theorem 1, p.4, and proof of Theorem 2, p.8 ('The endpoint q = 1 follows from Theorem 1').

import Mathlib
import Definitions.Def_KhintchineTwoRegime_sixProfile
import Definitions.Def_KhintchineTwoRegime_fourProfile
import Definitions.Def_KhintchineTwoRegime_Abound

theorem KhintchineTwoRegime.sixProfile_endpoint (n : ℕ) (hn : 4 ≤ n) :
    sixProfile n (Real.sqrt (2 - Real.sqrt 2)) =
      fourProfile n (Real.sqrt (2 - Real.sqrt 2)) ∧
    Abound ((2 - Real.sqrt (2 - Real.sqrt 2) ^ 2) / Real.sqrt 2) =
      1 / Real.sqrt 2 +
        (Real.sqrt (1 - Real.sqrt (2 - Real.sqrt 2) ^ 2 / 4) -
          Real.sqrt (2 - Real.sqrt 2)) *
          (Real.sqrt (2 - Real.sqrt 2) / (2 * Real.sqrt 2)) := by sorry
