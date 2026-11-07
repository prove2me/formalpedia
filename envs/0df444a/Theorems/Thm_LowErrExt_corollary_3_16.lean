-- Prove2me | Theorems.Thm_LowErrExt_corollary_3_16
-- name    : LowErrExt.corollary_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:43.241007+00:00
-- url     : https://prove2.me/theorems/fbae9f46-83c3-41fd-883a-6594d2c4ed18
-- title:
--   Corollary 3.16 — explicit linear seeded rank condensers (corrected: $k$ at least polylogarithmic)
-- statement:
--   There are a universal constant $\alpha>0$ and a constant $K\ge1$ such that the following holds. For all $n,k\in\mathbb N$ and $\delta>0$ with
--   $$k\ge K\big(\log_2(n+2)\cdot\log_2(2+1/\delta)\big)^{K},$$
--   there is a linear $k\to_\delta(1/2+\alpha)m$ seeded rank condenser $\mathrm{lsCond}:\mathbb F_2^n\times[D]\to\mathbb F_2^m$ with
--   $$m\ge\frac{k}{K\log_2(n+2)^{K}},\qquad D\le\frac nk\cdot K\big(\log_2(n+2)\,(1+1/\delta)\big)^{K}.$$
--   The family is explicit: one polynomial-time machine computes $\mathrm{lsCond}(x,y)$ from $1^k$, $1^{\lceil1/\delta\rceil}$, the seed $y$ in unary and $x$, and another computes $D$ from $1^n,1^k,1^{\lceil1/\delta\rceil}$.
--
--   Differences from the source:
--   - correction: for all k → for k ≥ K·(log₂(n+2)·log₂(2+1/δ))^K; reason: counterexample at k = 1, n ≥ 2, δ ≤ 1/4: m ≥ k/poly > 0 and the set {0, v} has dimension ≤ 1, so m = 1 and lsCond(v, y) = 1 on a 1 − δ fraction of seeds for each v ≠ 0; for independent v, w this gives lsCond(v + w, y) = 0 on a 1 − 2δ > δ fraction, contradicting the condition for v + w
--   - reading: explicit (undefined in the paper) → computed by one deterministic polynomial-time Turing machine (Mathlib TM2) on all inputs, chosen after the constants; reason: the standard meaning in the area; a per-n family would make the word empty, since such functions exist by counting
--   - reading: explicit lsCond with D seeds; δ given → the machine receives k, ⌈1/δ⌉ and the seed in unary (time polynomial in n and 1/δ), and a second machine outputs D; reason: the composition in Lemma 5.3 enumerates the seeds, so D must be computable; δ is a constant in every use
--   - encoding: poly(log n), poly((log n)/δ) → K·log₂(n+2)^K and K·(log₂(n+2)(1+1/δ))^K for one constant K ≥ 1; reason: every polynomial with nonnegative coefficients is bounded by K·x^K on x ≥ 1; n + 2 and 1 + 1/δ keep the bases ≥ 1 and change nothing up to K for δ ≤ 1
--   - encoding: real min-entropy threshold k → k ∈ ℕ; reason: for a linear condenser a set has H0 ≥ k iff its span has dimension ≥ ⌈k⌉, and the bounds for ⌈k⌉ imply those for k
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Corollary 3.16, p.25

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_LowErrExt_IsSeededRankCond
import Definitions.Def_LowErrExt_seededOfMachine

namespace LowErrExt

/-- **Corollary 3.16 (Explicit seeded rank condensers), corrected: `k` at least polylogarithmic.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Corollary 3.16, p.25: "For any δ > 0, there exists an explicit function lsCond : Fn2 × [D] → Fm2 that is
a linear k →δ (1/2 + α)m seeded rank condenser, where m ≥ k/poly(log n) and
D ≤ (n/k) · poly((log n)/δ)." Here α > 0 is a universal constant (Theorem 3.6, p.22).

**Formalization Note.**
1. Correction: the statement is for `k ≥ K·(log₂(n+2)·log₂(2 + 1/δ))^K`. As printed it fails at
   `k = 1`, `n ≥ 2`, `δ ≤ 1/4`: then `m ≥ 1`, and a linear `k →δ (1/2+α)m` condenser applied to
   `{0, v}` forces `m = 1` and `lsCond(v, y) = 1` for at least a `1 − δ` fraction of seeds for every
   `v ≠ 0`; for independent `v, w` this gives `lsCond(v + w, y) = 0` on at least a `1 − 2δ > δ`
   fraction of seeds, a contradiction.
2. "poly(x)" is `K·x^K` for one existential constant `K ≥ 1`, with `log n` read as `log₂(n + 2)` and
   `(log n)/δ` as `log₂(n + 2)·(1 + 1/δ)` (both `≥ 1`, and equal up to the constants absorbed in `K`
   for `δ ≤ 1`, `n ≥ 2`).
3. "Explicit": one polynomial-time machine `F` computes `lsCond(x, y)` from `1ᵏ`, `1ᵇ`, `1ʸ` and `x`,
   with `b = ⌈1/δ⌉`, and a second one `FD` computes `D` (in unary) from `1ⁿ, 1ᵏ, 1ᵇ`; so the
   construction is uniform in `n, k, δ` and runs in time polynomial in `n` and `1/δ`. `m` and `D`
   are functions of `(n, k, b)`. `k` is a natural number: for a linear condenser a set has
   `H0 ≥ k` iff its affine span has dimension `≥ ⌈k⌉`, so real `k` reduces to `⌈k⌉`. -/
theorem corollary_3_16 :
    ∃ α K : ℝ, 0 < α ∧ 1 ≤ K ∧
      ∃ F FD : List (List Bool) → List Bool, IsPolyTime F ∧ IsPolyTime FD ∧
        ∃ mf Df : ℕ → ℕ → ℕ → ℕ, ∀ (n k : ℕ) (δ : ℝ), 0 < δ →
          K * (Real.logb 2 (n + 2) * Real.logb 2 (2 + 1 / δ)) ^ K ≤ k →
            FD [List.replicate n true, List.replicate k true, List.replicate ⌈1 / δ⌉₊ true] =
                List.replicate (Df n k ⌈1 / δ⌉₊) true ∧
              (∀ (x : Fin n → ZMod 2) (y : Fin (Df n k ⌈1 / δ⌉₊)),
                (F [List.replicate k true, List.replicate ⌈1 / δ⌉₊ true, List.replicate y true,
                    bitsOf x]).length = mf n k ⌈1 / δ⌉₊) ∧
              IsLinearSeeded (seededOfMachine F (n := n) k ⌈1 / δ⌉₊ (mf n k ⌈1 / δ⌉₊)
                (Df n k ⌈1 / δ⌉₊)) ∧
              IsSeededRankCond k δ ((1 / 2 + α) * mf n k ⌈1 / δ⌉₊)
                (seededOfMachine F (n := n) k ⌈1 / δ⌉₊ (mf n k ⌈1 / δ⌉₊) (Df n k ⌈1 / δ⌉₊)) ∧
              (k : ℝ) / (K * Real.logb 2 (n + 2) ^ K) ≤ mf n k ⌈1 / δ⌉₊ ∧
              (Df n k ⌈1 / δ⌉₊ : ℝ) ≤
                (n : ℝ) / k * (K * (Real.logb 2 (n + 2) * (1 + 1 / δ)) ^ K) := by sorry

end LowErrExt
