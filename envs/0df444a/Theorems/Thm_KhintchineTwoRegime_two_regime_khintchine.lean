-- Prove2me | Theorems.Thm_KhintchineTwoRegime_two_regime_khintchine
-- name    : KhintchineTwoRegime.two_regime_khintchine
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:22.854598+00:00
-- url     : https://prove2.me/theorems/7c2f2d17-66cd-42a7-bc22-22b6de53491f
-- title:
--   The two-regime Khintchine inequality with sharp four- and six-coordinate profiles (Theorems 1 and 2)
-- statement:
--   On the proper chamber, with $\omega^*=(1/\sqrt2,1/\sqrt2,0,\dots,0)$ and $\mathcal C_n(\tau)$ the proper unit vectors at distance $\tau$ from $\omega^*$:
--
--   1. for every $n\ge2$, every $\tau$ and every $\omega\in\mathcal C_n(\tau)$,
--   $$
--   K_n(\omega)\ \ge\ \frac1{\sqrt2}+\Bigl(\sqrt{1-\frac{\tau^2}4}-\tau\Bigr)\frac{\tau}{2\sqrt2};
--   $$
--   2. for every $n\ge4$ and $0\le\tau\le\sqrt{2-\sqrt2}$, the four-coordinate profile $\omega_\tau=(r,r,s,s,0,\dots,0)$ lies in $\mathcal C_n(\tau)$, attains this bound, and is the only point of $\mathcal C_n(\tau)$ that does;
--   3. for every $n\ge6$ and $\tau\in\bigl[\sqrt{2-\sqrt2},\sqrt{2-\sqrt{966}/22}\bigr]$, the six-coordinate profile $\omega^{(6)}_\tau=(r,r,r,r,s,s,0,\dots,0)$ is the unique minimizer of $K_n$ on $\mathcal C_n(\tau)$, and
--   $$
--   \min_{\omega\in\mathcal C_n(\tau)}K_n(\omega)=\frac{3q}4+\frac3{8\sqrt2}\sqrt{1-q^2},\qquad q=\frac{2-\tau^2}{\sqrt2};
--   $$
--   4. $0.7663211842<\sqrt{2-\sqrt{966}/22}<0.7663211843$.
--
--   This is the paper's main result, eq. (3), "and the sharp profiles at which the strict equality is obtained": the minimal first absolute moment on $\mathcal C_n(\tau)$ switches from a four-coordinate to a six-coordinate profile at $\tau=\sqrt{2-\sqrt2}$, with a square-root change of rate.
--
--   Differences from the source:
--   - generalization: eq. (3): the two lower bounds, and the sharp profiles at which equality is obtained → every clause of Theorems 1 and 2: the bound for all n ≥ 2, optimality and equality iff ω = ω_τ for n ≥ 4, unique minimizer and minimum for n ≥ 6, and the decimal value of d₁; reason: the conjunction of Theorems 1 and 2 at full strength; it contains both inequalities of (3) and identifies the profiles
--   - encoding: optimality, equality iff, unique minimizer, minimum value → membership of the profile in C_n(τ), attainment/minimality, uniqueness as equality of vectors, value of K at the profile; reason: these clauses are the definitions of the printed notions
--   - encoding: d₁ = 0.7663211842… → 7663211842/10¹⁰ < d₁ < 7663211843/10¹⁰; reason: a truncated decimal expansion means exactly this two-sided bound
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §1.1, eq. (3), pp.2–3; Theorem 1, p.4; Theorem 2, p.8

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_fourProfile
import Definitions.Def_KhintchineTwoRegime_sixProfile
import Definitions.Def_KhintchineTwoRegime_Abound

namespace KhintchineTwoRegime

/-- The two-regime Khintchine inequality with its sharp profiles (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (3), §1.1, pp.2–3;
Theorem 1, p.4; Theorem 2, p.8). On the proper chamber:
1. for every `n ≥ 2` and `ω ∈ C_n(τ)`, `K_n(ω) ≥ 1/√2 + (√(1 − τ²/4) − τ) · τ/(2√2)`;
2. for `n ≥ 4` and `0 ≤ τ ≤ √(2 − √2)`, the four-coordinate profile `ω_τ` lies in `C_n(τ)`,
   attains the bound, and is the only point of `C_n(τ)` that does;
3. for `n ≥ 6` and `τ ∈ [√(2 − √2), √(2 − √966/22)]`, the six-coordinate profile
   `ω_τ^{(6)}` is the unique minimizer of `K_n` on `C_n(τ)`, with minimum
   `3q/4 + (3/(8√2))√(1 − q²)`, `q = (2 − τ²)/√2`;
4. `0.7663211842 < √(2 − √966/22) < 0.7663211843`.

**Formalization Note** This is Theorem 1 ∧ Theorem 2 with every clause; see those items for the
conventions (Euclidean norm `l2Norm`, 0-based indices, uniform average over sign vectors). -/
theorem two_regime_khintchine :
    (∀ n : ℕ, 2 ≤ n → ∀ τ : ℝ, ∀ ω ∈ Cn n τ,
      1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ≤ K n ω) ∧
    (∀ n : ℕ, 4 ≤ n → ∀ τ : ℝ, 0 ≤ τ → τ ≤ Real.sqrt (2 - Real.sqrt 2) →
      fourProfile n τ ∈ Cn n τ ∧
      K n (fourProfile n τ) =
        1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ∧
      ∀ ω ∈ Cn n τ,
        K n ω = 1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) →
          ω = fourProfile n τ) ∧
    (∀ n : ℕ, 6 ≤ n →
      ∀ τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22)),
        sixProfile n τ ∈ Cn n τ ∧
        (∀ ω ∈ Cn n τ, K n (sixProfile n τ) ≤ K n ω) ∧
        (∀ ω ∈ Cn n τ, K n ω = K n (sixProfile n τ) → ω = sixProfile n τ) ∧
        K n (sixProfile n τ) = Abound ((2 - τ ^ 2) / Real.sqrt 2)) ∧
    ((7663211842 : ℝ) / 10 ^ 10 < Real.sqrt (2 - Real.sqrt 966 / 22) ∧
      Real.sqrt (2 - Real.sqrt 966 / 22) < (7663211843 : ℝ) / 10 ^ 10) := by sorry

end KhintchineTwoRegime
