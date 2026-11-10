-- Prove2me | Theorems.Thm_NearOptOWF_max_load_random_function
-- name    : NearOptOWF.max_load_random_function
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:26.710343+00:00
-- url     : https://prove2.me/theorems/228ca47d-c959-49af-b4b8-94e442b83c77
-- title:
--   Proof of Lemma 4.10 — max load of a random function: $\Pr_R[\max_y|R^{-1}(y)|\ge nm\cdot\max\{1,2^{n-m}\}]\le 2^{-\Omega(nm)}$
-- statement:
--   Let $R : \{0,1\}^n \to \{0,1\}^m$ be a uniformly random function. There are $c > 0$ and $n_0$ such that for all $n \ge n_0$ and all $m$,
--   $$
--   \Pr_R\Bigl[\max_y |R^{-1}(y)| \ge nm \cdot \max\{1, 2^{n-m}\}\Bigr] \le 2^{-c\,nm}.
--   $$
--
--   This bound on the maximum load is what lets the proof of Lemma 4.10 compare inverting $f(x)$ for random $x$ with inverting a random $y$.
--
--   Differences from the source:
--   - reading: 2^{-Ω(nm)} (with "for sufficiently large n" in the proof) → ∃ c > 0 and n₀, placed before m, bound 2^{-c·n·m} for all n ≥ n₀ and all m; reason: the hidden constant of Ω(nm) is explicit and uniform in m, as the proof gives it
--   - encoding: probability over a random function R : {0,1}ⁿ → {0,1}ᵐ → the fraction of all functions (Fin n → Bool) → (Fin m → Bool) with the property; reason: a uniform random function is the uniform distribution on the finite function space
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), proof of Lemma 4.10, max-load display, p.18 (PDF p.20)

import Mathlib

namespace NearOptOWF

/-- **Max load of a random function** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), proof of Lemma 4.10, p.18 (PDF p.20): "Let `R :
{0,1}ⁿ → {0,1}ᵐ` be a random function. We show that `Pr_R[max_y |R⁻¹(y)| ≥ nm · max{1, 2^{n−m}}] ≤
2^{−Ω(nm)}`"): there are `c > 0` and `n₀` such that for all `n ≥ n₀` and all `m`, the fraction of
functions `R : {0,1}ⁿ → {0,1}ᵐ` having a value `y` with at least `nm · max{1, 2^{n−m}}` pre-images is at
most `2^{−c·n·m}`.

**Formalization Note** `2^{−Ω(nm)}` is `∃ c > 0` (and a threshold `n₀`), placed before `m`. With natural
subtraction, `2^{n−m}` is `1` when `m ≥ n`, so `max 1 (2^(n−m))` is the paper's `max{1, 2^{n−m}}`. -/
theorem max_load_random_function :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ n →
      ((Finset.univ.filter fun R : (Fin n → Bool) → (Fin m → Bool) =>
          ∃ y : Fin m → Bool,
            n * m * max 1 (2 ^ (n - m)) ≤ (Finset.univ.filter fun x => R x = y).card).card : ℝ) /
        (Fintype.card ((Fin n → Bool) → (Fin m → Bool)) : ℝ) ≤ (2 : ℝ) ^ (-(c * n * m)) := by sorry

end NearOptOWF
