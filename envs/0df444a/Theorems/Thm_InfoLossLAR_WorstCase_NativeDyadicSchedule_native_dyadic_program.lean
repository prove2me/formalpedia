-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_NativeDyadicSchedule_native_dyadic_program
-- name    : InfoLossLAR.WorstCase.NativeDyadicSchedule.native_dyadic_program
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:26:09.703697+00:00
-- url     : https://prove2.me/theorems/bfc64a98-033f-4f8d-a705-8fd5fd4b3d5a
-- title:
--   Binary-time dyadic source-width selection for fixed-family DGS
-- statement:
--   For the scan `result` on a positive rational initial width $W$, positive rational target width $r$ and positive integer dimension $n$, there is a single total polynomial-time multi-stack Turing program in the platform's binary encoding that returns the scan's index $k$ and rational width $u$.
--
--   Let $q,\eta>0$, put $\sigma=n+2$, and suppose
--
--   $$
--   r\ge \frac{16q\sqrt n}{\sigma}\eta,\qquad
--   W\ge\frac{r\sigma}{\sqrt2\sqrt n}.
--   $$
--
--   The returned $k$ is at most the sum of the binary length of the absolute numerator of $W$ and the binary length of the denominator of $r$. Every preceding dyadic width $W/2^j$ and the returned width $u$ strictly exceed $\sqrt2q\eta$. In addition,
--
--   $$
--   \frac{\sqrt n}{\sqrt2r}\le\frac{\sigma}{2u},
--   \qquad \frac1{\sqrt2(1/(\sqrt2r))}=r.
--   $$
--
--   The program compares rational squares and does not compute a square root or expand $W$, $r$ or $n$ in unary. The theorem establishes a width-selection interface only; it does not construct the initial lattice sampler, BDD oracle or quantum iteration.
--
--   **Formalization Note.** Polynomial time uses the native `Automatic.enc` for rational pairs, naturals and outputs. A separate encoding bridge is needed to compose this program with the platform's `encMat`, `encQ` and quantum circuit interfaces.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.2, 3.3, 3.14, pp. 18–19 and 26–27. This is a separately proved binary-time fixed-family width-selection and terminal-step statement; the source does not specify this implementation.

import Definitions.Def_RegevDyadicSchedule
set_option autoImplicit false
open InfoLossLAR.WorstCase.NativeDyadicSchedule
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace InfoLossLAR.WorstCase.NativeDyadicSchedule
theorem native_dyadic_program :
    Nonempty (Turing.TM2ComputableInPolyTime Automatic.enc Automatic.enc result) ∧
      ∀ (x : Input) (q eta : ℝ),
        0 < x.2 → 0 < x.1.1 → 0 < x.1.2 → 0 < q → 0 < eta →
        (16*q*Real.sqrt x.2/((x.2 : ℝ)+2))*eta ≤ (x.1.2 : ℝ) →
        (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2) ≤ (x.1.1 : ℝ) →
        crossingIndex x ≤ (ticks x).length ∧
          (∀ j < crossingIndex x, Real.sqrt 2*q*eta < (width (x,j) : ℝ)) ∧
          Real.sqrt 2*q*eta < (selectedWidth x : ℝ) ∧
          Real.sqrt x.2/(Real.sqrt 2*(x.1.2 : ℝ)) ≤
            ((x.2 : ℝ)+2)/(2*(selectedWidth x : ℝ)) ∧
          1/(Real.sqrt 2*(1/(Real.sqrt 2*(x.1.2 : ℝ)))) = (x.1.2 : ℝ) := by sorry
end InfoLossLAR.WorstCase.NativeDyadicSchedule
