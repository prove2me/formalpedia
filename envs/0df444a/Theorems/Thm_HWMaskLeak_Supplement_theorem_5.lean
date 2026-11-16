-- Prove2me | Theorems.Thm_HWMaskLeak_Supplement_theorem_5
-- name    : HWMaskLeak.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:02:38.289617+00:00
-- url     : https://prove2.me/theorems/61c8f87b-f69d-44fd-be4c-79de4553bdaf
-- title:
--   Theorem 5 — near-dyadic lower bound: $\max_sE_k(s)\ge$ RMS $\ge\frac12L^{1/2}25^{-k}n^{-k/2}$
-- statement:
--   Let $E_k(s)$ be the insecurity of a uniform $k$-party additive sharing of $s\in\mathbb Z/N\mathbb Z$ under Hamming-weight leakage, eq. (1).
--
--   There is an absolute constant $C>0$ such that the following hold.
--
--   1. Let $k\ge2$ and $n\ge4$ be integers, let $m\in[0,n-1]$ be real, and let $N$ be an integer with $|N-2^n|\le2^m$. Then
--   $$
--   \max_{0\le s<N}E_k(s)\ \ge\ \sqrt{\frac1N\sum_{0\le s<N}E_k(s)^2}\ \ge\ \frac12\cdot L^{1/2}\cdot(1/25)^k\cdot n^{-k/2},
--   \qquad L=\Bigl(n-m-\tfrac12\log_2 n-C\Bigr)_+,
--   $$
--   where $(x)_+=\max\{0,x\}$.
--   2. In particular, for every $\varepsilon>0$ there is $n_0$ such that for all $n\ge n_0$: when $m=(1-\varepsilon)n$ (with the hypotheses of part 1) and $\varepsilon n\ge\log_2 n+2C$,
--   $$
--   \max_{0\le s<N}E_k(s)\ \ge\ \frac{1}{2\sqrt2}\cdot\varepsilon^{1/2}\cdot(1/25)^k\cdot n^{-k/2+1/2}.
--   $$
--
--   The theorem shows that the $n^{-1/2}$-per-share decay of the upper bounds cannot be improved, on average over secrets, for moduli near a power of two.
--
--   **Formalization Note** $2^m$ and the powers of $n$ are real powers; $\log_2$ is `Real.logb 2`; the root-mean-square is $\sqrt{(1/N)\sum_{s}E_k(s)^2}$ over $s\in\mathbb Z/N\mathbb Z$.
--
--   Differences from the source:
--   - encoding: N an integer with |N − 2ⁿ| ≤ 2^m → N : ℕ with [NeZero N]; reason: with m ≤ n − 1 the hypothesis forces N ≥ 2ⁿ − 2^{n−1} ≥ 8 (footnote 5 of the paper), so no admissible N is excluded
--   - encoding: C > 0 is an absolute constant (in L and in εn ≥ log₂ n + 2C) → ∃ C > 0 chosen before k, n, m, N, ε, the same C in both parts; reason: the paper's C is a single absolute constant used in both parts
--   - encoding: max_{0≤s<N} E_k(s) ≥ x → ∃ s : ZMod N, x ≤ insecurity N k s; reason: a maximum over a finite nonempty set is at least x iff some element is
--   - reading: for sufficiently large n, as a function of ε → ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀ (n₀ independent of k, N); reason: the threshold depends on ε only, as the page says
--   - encoding: m = (1 − ε)n ∈ [0, n − 1] (ε implicitly positive) → explicit 0 < ε together with 0 ≤ (1 − ε)n ≤ n − 1; reason: (1 − ε)n ≤ n − 1 already forces ε ≥ 1/n > 0, so 0 < ε excludes nothing
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360358eddae84b7b4ee1bbb418105b7887539046e553046bbedd46125a9), Theorem 5, p.28 (pdf p.28), §5.2; proof in Appendix F

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity

namespace HWMaskLeak.Supplement

open HWMaskLeak

/-- **Theorem 5 (near-dyadic lower bound)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Theorem 5, p.28): there is an absolute constant
`C > 0` such that the following holds. Let `k ⩾ 2` and `n ⩾ 4` be integers, `m ∈ [0, n − 1]` real, and
`N` an integer with `|N − 2ⁿ| ⩽ 2^m`. Then
`max_{0⩽s<N} E_k(s) ⩾ √((1/N) Σ_{0⩽s<N} E_k(s)²) ⩾ ½ · L^{1/2} · (1/25)^k · n^{−k/2}`, where
`L = (n − m − ½ log₂ n − C)_+`. In particular, when `m = (1 − ε)n` and `εn ⩾ log₂ n + 2C`, then for
sufficiently large `n` (as a function of `ε`),
`max_{0⩽s<N} E_k(s) ⩾ (1/(2√2)) · ε^{1/2} · (1/25)^k · n^{−k/2+1/2}`.

**Formalization Note** `E_k(s)` is the published `insecurity N k s` (eq. (1)). `max_s E_k(s) ⩾ x` is
written `∃ s, x ⩽ E_k(s)`. The same `C` appears in `L` and in the hypothesis of the second part, and
is chosen before `k, n, m, N, ε`; the threshold `n₀` depends on `ε` only. `2^m` and the powers of `n`
are real powers, `log₂` is `Real.logb 2`. The hypotheses force `N ⩾ 2^{n−1} ⩾ 8`, so `N` is a
natural number and `[NeZero N]` excludes nothing. -/
theorem theorem_5 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (k n : ℕ) (m : ℝ) (N : ℕ) [NeZero N], 2 ≤ k → 4 ≤ n → 0 ≤ m → m ≤ (n : ℝ) - 1 →
        |(N : ℝ) - 2 ^ n| ≤ (2 : ℝ) ^ m →
        (∃ s : ZMod N, Real.sqrt ((1 / (N : ℝ)) * ∑ t : ZMod N, insecurity N k t ^ 2) ≤
            insecurity N k s) ∧
        (1 / 2 : ℝ) * Real.sqrt (max 0 ((n : ℝ) - m - (1 / 2) * Real.logb 2 n - C)) *
            ((1 : ℝ) / 25) ^ k * (n : ℝ) ^ (-(k : ℝ) / 2) ≤
          Real.sqrt ((1 / (N : ℝ)) * ∑ t : ZMod N, insecurity N k t ^ 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (k n : ℕ) (N : ℕ) [NeZero N], n₀ ≤ n → 2 ≤ k → 4 ≤ n →
        0 ≤ (1 - ε) * n → (1 - ε) * n ≤ (n : ℝ) - 1 →
        |(N : ℝ) - 2 ^ n| ≤ (2 : ℝ) ^ ((1 - ε) * n) →
        Real.logb 2 n + 2 * C ≤ ε * n →
        ∃ s : ZMod N, 1 / (2 * Real.sqrt 2) * Real.sqrt ε * ((1 : ℝ) / 25) ^ k *
            (n : ℝ) ^ (-(k : ℝ) / 2 + 1 / 2) ≤ insecurity N k s) := by sorry

end HWMaskLeak.Supplement
