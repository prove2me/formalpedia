-- Prove2me | Theorems.Thm_LawLocalComp_lemma_2_5
-- name    : LawLocalComp.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:13.559676+00:00
-- url     : https://prove2.me/theorems/0614fd2b-49ae-49f9-8678-00bc297a9b05
-- title:
--   Lemma 2.5 (Affine-gap tests)
-- statement:
--   1. If $f$ is twice differentiable on $[x_0,x_0+w]$, $w>0$, with $f''\ge\kappa$, then every affine $\ell$ has $\sup_{[x_0,x_0+w]}|f-\ell|\ge\kappa w^2/16$.
--   2. If $H$ is affine and nonnegative on $[u,v]$ and $0<u<w<v$, then $H(w)\le H(u)+(w/v)H(v)$.
--   3. For fixed $s,c,C>0$ there is $c'>0$ such that for every integer $M\ge1$: if $c(\log_2k)^s\le H(k)\le C(\log_2k)^s$ for all integers $1\le k\le M$, then any $p$ closed intervals covering $[1,M]$, on each of which $H$ is affine, satisfy
--   $$p\ \ge\ c'\log\log(M+2).$$
--
--   Parts 1 and 3 are the tests that force atoms in all lower bounds: an output with few atoms has a piecewise affine envelope that cannot follow a curved or polylogarithmic target.
--
--   **Formalization Note** Derivatives on the closed interval are taken within the interval; $\log_2 k$ is `Real.logb 2 k` raised to the real power $s$.
--
--   Differences from the source:
--   - generalization: H needs Ω_{s,c,C}(log log(M + 2)) affine pieces → every cover of [1, M] by p closed intervals on each of which H is affine has p ≥ c' log log(M + 2); reason: a partition into p affine pieces is such a cover, so the cover form implies the printed one
--   - reading: on integers k ≤ M → for integers 1 ≤ k ≤ M, with M ≥ 1; reason: (log₂ k)^s is undefined at k = 0
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 2.5, p.5

import Mathlib

namespace LawLocalComp

/-- **Lemma 2.5 (Affine-gap tests).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 2.5, p.5.

(a) A function twice differentiable on `[x₀, x₀ + w]` with second derivative at least `κ` has, against
every affine function, uniform error at least `κw²/16`. (b) For `H` affine and nonnegative on `[u, v]`
and `0 < u < w < v`, `H(w) ≤ H(u) + (w/v)H(v)`. (c) For fixed `s, c, C > 0`, if
`c(log₂ k)^s ≤ H(k) ≤ C(log₂ k)^s` at the integers `1 ≤ k ≤ M`, then any family of intervals covering
`[1, M]` on each of which `H` is affine has `Ω_{s,c,C}(log log(M + 2))` members.

**Formalization Note.** Derivatives on the closed interval are `derivWithin`. "Needs … affine pieces"
is a lower bound on the number `p` of closed intervals, covering `[1, M]`, on each of which `H` is
affine; a partition into `p` pieces is such a cover. `log₂ k` is `Real.logb 2 k` and the power is
`rpow`. -/
theorem lemma_2_5 :
    (∀ (f : ℝ → ℝ) (x₀ w κ : ℝ), 0 < w → DifferentiableOn ℝ f (Set.Icc x₀ (x₀ + w)) →
      DifferentiableOn ℝ (derivWithin f (Set.Icc x₀ (x₀ + w))) (Set.Icc x₀ (x₀ + w)) →
      (∀ x ∈ Set.Icc x₀ (x₀ + w),
        κ ≤ derivWithin (derivWithin f (Set.Icc x₀ (x₀ + w))) (Set.Icc x₀ (x₀ + w)) x) →
      ∀ α₀ α₁ : ℝ, ∃ x ∈ Set.Icc x₀ (x₀ + w), κ * w ^ 2 / 16 ≤ |f x - (α₀ + α₁ * x)|) ∧
    (∀ (H : ℝ → ℝ) (u w v : ℝ), 0 < u → u < w → w < v →
      (∃ α₀ α₁ : ℝ, ∀ x ∈ Set.Icc u v, H x = α₀ + α₁ * x) → (∀ x ∈ Set.Icc u v, 0 ≤ H x) →
      H w ≤ H u + (w / v) * H v) ∧
    (∀ s c C : ℝ, 0 < s → 0 < c → 0 < C → ∃ c' : ℝ, 0 < c' ∧
      ∀ M : ℕ, 1 ≤ M → ∀ (H : ℝ → ℝ) (p : ℕ) (I : Fin p → ℝ × ℝ),
        Set.Icc (1 : ℝ) M ⊆ ⋃ i, Set.Icc (I i).1 (I i).2 →
        (∀ i, ∃ α₀ α₁ : ℝ, ∀ x ∈ Set.Icc (I i).1 (I i).2, H x = α₀ + α₁ * x) →
        (∀ k : ℕ, 1 ≤ k → k ≤ M →
          c * Real.logb 2 k ^ s ≤ H k ∧ H k ≤ C * Real.logb 2 k ^ s) →
        c' * Real.log (Real.log (M + 2)) ≤ p) := by sorry

end LawLocalComp
