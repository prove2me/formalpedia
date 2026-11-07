-- Prove2me | Theorems.Thm_IterRoundDet_theorem_1_1
-- name    : IterRoundDet.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:37.419639+00:00
-- url     : https://prove2.me/theorems/e92e943f-ff8c-4739-b19c-a68160cc3498
-- title:
--   Theorem 1.1 — a polynomial-time algorithm finds a matroid base within $e^{14d+\varepsilon}$ of optimal for a multiaffine real stable $p$
-- statement:
--   Let $p(z_1,\dots,z_n)$ be a homogeneous multiaffine real stable polynomial of degree $d$, and let $\mathcal M$ be a matroid on $[n]$ of rank $r\ge d$ given by an independence oracle. For any $\varepsilon>0$, there is a polynomial-time algorithm that returns a base $B\in\mathcal B(\mathcal M)$ such that
--
--   $$\log p(\mathbf 1_B)\ge\max_{B^*\in\mathcal B(\mathcal M)}\log p(\mathbf 1_{B^*})-14d-\varepsilon.$$
--
--   The algorithm is deterministic given a value oracle for $p$, and succeeds with high probability given a coefficient oracle for $p$ and an independence oracle for its support matroid $\mathcal N$.
--
--   This is the main result of the paper. Taking $p(z)=\det(\sum_i z_iv_iv_i^\top)$ gives determinant maximization under a general matroid.
--
--   **Formalization Note** The statement is the conjunction of the two access models, each with one finite program and one pair of constants chosen before the instance and before $\varepsilon,\rho$. It runs on the log-cost oracle RAM of `IterRoundDet.Machine`, with $T=C(2+n+b+N)^K$, $N=\lceil 1/\varepsilon\rceil$, plus $L=\lceil\log_2(1/\rho)\rceil$ in the second clause. Time holds on every coin tape, and success is counted over tapes.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - reading: a polynomial-time algorithm, no machine named → one finite program on a log-cost oracle RAM, with C and K before the instance; time C(2+n+b+N)^K; reason: the paper counts bits (pp.19, 21, 41); every reasonable bit model gives the same class
--   - encoding: independence, value and coefficient oracles → tagged query instructions, rationals as (zigzag numerator, denominator), sets as characteristic words, ill-formed queries answered by zeros; reason: a syntactic program needs a concrete layout; no instance changes
--   - reading: for any ε > 0 (and ρ ∈ (0,1)), an algorithm → one program for all real ε, ρ, reading N = ⌈1/ε⌉₊ and L = ⌈log₂(1/ρ)⌉₊ from the input; reason: uniform in ε and ρ, which is what polynomial in 1/ε and log(1/ρ) on p.19 says; it implies the fixed-ε form
--   - reading: a value oracle for p, with b the maximum bit length of the coefficients → the value clause also assumes AnswerBits b c: the answer p(z) has at most 2b + n + 2∑(bits of z_i) bits; reason: a bit-counting algorithm must read the answers, so the page presupposes polynomial-length answers; a common denominator of b bits implies this (integer coefficients, rational determinants), proved in the sanity file
--   - reading: succeeds with probability at least 1 − ρ, in polynomial time → time on every coin tape; success counted over tapes as (1 − ρ)2^T ≤ #{good tapes}; reason: the proofs cap every loop and report failure as an outcome (p.40); a time bound on every tape is the stronger form
--   - encoding: log p(1_B) ≥ max log p(1_B*) − 14d − ε, with log 0 = −∞ → e^{−14d−ε} p(1_B*) ≤ p(1_B) for every base B*; reason: equivalent under the page's convention (p.6), including max = 0; Real.log 0 = 0 would corrupt the logarithmic form
--   - encoding: a matroid M on [n] of rank r ≥ d → M : Matroid (Fin n), M.E = univ, (d : ℕ∞) ≤ M.eRank; reason: Mathlib form; r is not an input, as the greedy algorithm computes it
--   - encoding: returns a base B → out = some (setCode B) with M.IsBase B; reason: the output of a machine is a list of cells
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 1.1 and footnote 2, p.2; §4, p.19

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Machine
import Definitions.Def_IterRoundDet_Oracles

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 1.1 (Real stable polynomial maximization), p.2. Let `p` be a homogeneous multiaffine real stable polynomial
of degree `d`, and `M` a matroid on `[n]` of rank `r ≥ d` given by an independence oracle. For any `ε > 0`, there is a polynomial-time
algorithm that returns a base `B ∈ B(M)` with `log p(1_B) ≥ max_{B*∈B(M)} log p(1_{B*}) − 14d − ε`. The algorithm is deterministic
given a value oracle for `p`, and succeeds with high probability given a coefficient oracle for `p` and an independence oracle for
its support matroid `N`.

**Formalization Note.** A conjunction of the two clauses, each with one program and one `C, K` before the instance and before `ε, ρ`.
Time is log-cost on the machine of `IterRoundDet.Machine` with answers charged, polynomial in `n, b, N = ⌈1/ε⌉₊` (and `L = ⌈log₂(1/ρ)⌉₊`),
and it holds on every tape. The conclusion is multiplicative, `e^{−14d−ε} p(1_{B*}) ≤ p(1_B)` for every base `B*`, which is the printed
line under the page's convention `log 0 = −∞` (and `Real.log 0 = 0` would corrupt it). The value clause assumes that the oracle's
answers have polynomial length (`AnswerBits`). -/
theorem theorem_1_1 :
    (∃ (P : Program) (C K : ℕ), CoinFree P ∧
      ∀ (n d b : ℕ) (c : Finset (Fin n) → ℚ) (M : Matroid (Fin n)) (ε : ℝ),
        IsStablePoly d (castCoef c) → M.E = Set.univ → (d : ℕ∞) ≤ M.eRank →
        BitBounded b c → AnswerBits b c → 0 < ε →
        let N := ⌈1 / ε⌉₊
        let T := C * (2 + n + b + N) ^ K
        let s := run P (valueModel M c) [n, d, b, N] (fun _ => false) T
        s.out.isSome ∧ s.cost ≤ T ∧ ∃ B : Finset (Fin n), s.out = some (setCode B) ∧
          M.IsBase (B : Set (Fin n)) ∧
          ∀ B' : Finset (Fin n), M.IsBase (B' : Set (Fin n)) →
            Real.exp (-(14 * d) - ε) * pEval (castCoef c) (ind B') ≤ pEval (castCoef c) (ind B)) ∧
    (∃ (P : Program) (C K : ℕ),
      ∀ (n d b : ℕ) (c : Finset (Fin n) → ℚ) (M : Matroid (Fin n)) (ε ρ : ℝ),
        IsStablePoly d (castCoef c) → M.E = Set.univ → (d : ℕ∞) ≤ M.eRank →
        BitBounded b c → 0 < ε → 0 < ρ → ρ < 1 →
        let N := ⌈1 / ε⌉₊
        let L := ⌈Real.logb 2 (1 / ρ)⌉₊
        let T := C * (2 + n + b + N + L) ^ K
        let input := [n, d, b, N, L]
        (∀ w : Fin T → Bool,
          (run P (coeffModel M c) input (extendBits w) T).out.isSome ∧
          (run P (coeffModel M c) input (extendBits w) T).cost ≤ T) ∧
        (1 - ρ) * (2 : ℝ) ^ T ≤ (Nat.card {w : Fin T → Bool //
          ∃ B : Finset (Fin n),
            (run P (coeffModel M c) input (extendBits w) T).out = some (setCode B) ∧
            M.IsBase (B : Set (Fin n)) ∧
            ∀ B' : Finset (Fin n), M.IsBase (B' : Set (Fin n)) →
              Real.exp (-(14 * d) - ε) * pEval (castCoef c) (ind B') ≤
                pEval (castCoef c) (ind B)} : ℝ)) := by sorry

end IterRoundDet
