-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_NativeDyadicSchedule_native_initial_program
-- name    : InfoLossLAR.WorstCase.NativeDyadicSchedule.native_initial_program
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:36:13.436314+00:00
-- url     : https://prove2.me/theorems/8b4eb748-e557-47ca-b49d-315150b698b0
-- title:
--   Binary-time initial base and dyadic source-width selection
-- statement:
--   There is a single total polynomial-time multi-stack Turing program which, on binary-coded integer rows, a rational requested width $r$ and a natural dimension $n$, computes the fixed-family initializer base, the dyadic crossing index and its selected rational width.
--
--   For $n\ge1$, $r,q,\eta>0$, assume
--
--   $$
--   r\ge\frac{16q\sqrt n}{n+2}\,\eta.
--   $$
--
--   The output base $b$ satisfies $b\ge2$, $b\ge n$ and $b\ge r(n+2)$. Its associated width $W=b(1+\sum_{i,j}|B_{ij}|)$ is positive. The output index $k$ is at most the sum of the binary lengths of the numerator of $W$ and denominator of $r$, every preceding width $W/2^j$ and the selected width $u$ exceed $\sqrt2q\eta$, and
--
--   $$
--   \frac{\sqrt n}{\sqrt2r}\le\frac{n+2}{2u}.
--   $$
--
--   The list of rows need not encode a square or nonsingular matrix for these arithmetic properties. The program uses rational square comparison and binary representations; it does not expand $b$ as a unary list. It does not construct the lattice Gaussian pool, BDD oracle or quantum iteration.
--
--   **Formalization Note.** The program is polynomial time in `Automatic.enc` for row lists, rationals, naturals and outputs. Its link to the platform `encMat`/`encQ` input and the actual initializer's TM2/quantum sampler remains a separate proof obligation.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.2, 3.3 and 3.14. This is a binary fixed-family initialization and dyadic-width interface derived for the formalization, not a verbatim algorithm in that source.

import Definitions.Def_RegevInitialSelection
set_option autoImplicit false
open InfoLossLAR.WorstCase.NativeDyadicSchedule
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace InfoLossLAR.WorstCase.NativeDyadicSchedule
theorem native_initial_program :
    Nonempty (Turing.TM2ComputableInPolyTime Automatic.enc Automatic.enc initialSelection) ∧
      ∀ (x : InitialInput) (q eta : ℝ),
        0 < x.2 → 0 < x.1.2 → 0 < q → 0 < eta →
        (16*q*Real.sqrt x.2/((x.2 : ℝ)+2))*eta ≤ (x.1.2 : ℝ) →
        2 ≤ initialBase x.1.2 x.2 ∧ x.2 ≤ initialBase x.1.2 x.2 ∧
          (x.1.2 : ℝ)*((x.2 : ℝ)+2) ≤ initialBase x.1.2 x.2 ∧
          0 < (initialRequest x).1.1 ∧
          crossingIndex (initialRequest x) ≤
            Nat.size ((initialRequest x).1.1).num.natAbs + Nat.size x.1.2.den ∧
          (∀ j < crossingIndex (initialRequest x),
            Real.sqrt 2*q*eta < (width (initialRequest x,j) : ℝ)) ∧
          Real.sqrt 2*q*eta < (selectedWidth (initialRequest x) : ℝ) ∧
          Real.sqrt x.2/(Real.sqrt 2*(x.1.2 : ℝ)) ≤
            ((x.2 : ℝ)+2)/(2*(selectedWidth (initialRequest x) : ℝ)) := by sorry
end InfoLossLAR.WorstCase.NativeDyadicSchedule
