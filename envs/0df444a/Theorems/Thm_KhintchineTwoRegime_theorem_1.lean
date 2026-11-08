-- Prove2me | Theorems.Thm_KhintchineTwoRegime_theorem_1
-- name    : KhintchineTwoRegime.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:34.047266+00:00
-- url     : https://prove2.me/theorems/345a1175-ed17-4ca6-a12f-dae87df95e4b
-- title:
--   Theorem 1 — four-coordinate regime: sharp bound, attained exactly at $\omega_\tau$ for $\tau\le\sqrt{2-\sqrt2}$
-- statement:
--   Let $n\ge2$ and $\tau\in\mathbb R$. For every proper unit vector $\omega\in\mathcal C_n(\tau)$, i.e. at Euclidean distance $\tau$ from $\omega^*=(1/\sqrt2,1/\sqrt2,0,\dots,0)$,
--   $$
--   K_n(\omega)\ \ge\ \frac1{\sqrt2}+\Bigl(\sqrt{1-\frac{\tau^2}{4}}-\tau\Bigr)\frac{\tau}{2\sqrt2}.
--   $$
--   Moreover, when $n\ge4$ the estimate is optimal for $0\le\tau\le\sqrt{2-\sqrt2}$: in that range
--
--   1. the four-coordinate profile $\omega_\tau=(r,r,s,s,0,\dots,0)$, $r=(1-\tau^2/2)/\sqrt2$, $s=(\tau/\sqrt2)\sqrt{1-\tau^2/4}$, lies in $\mathcal C_n(\tau)$;
--   2. $K_n(\omega_\tau)$ equals the bound;
--   3. equality at a point $\omega\in\mathcal C_n(\tau)$ holds only if $\omega=\omega_\tau$.
--
--   This is the first regime of the two-regime Khintchine inequality: near the classical minimizer the extremal vectors stay four-dimensional and grouped in equal pairs.
--
--   **Formalization Note** $n\ge2$ is the standing assumption of §2. On $\mathcal C_n(\tau)$ one has $\tau^2\le2$, so the radicand $1-\tau^2/4$ is positive.
--
--   Differences from the source:
--   - encoding: the estimate is optimal; equality holds if and only if ω = ω_τ → ω_τ ∈ C_n(τ), K_n(ω_τ) equals the bound, and equality at ω ∈ C_n(τ) implies ω = ω_τ; reason: the three clauses are exactly attainment and the two directions of the iff
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 1, p.4

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_fourProfile

namespace KhintchineTwoRegime

/-- Theorem 1 (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), p.4): for every `ω ∈ C_n(τ)`,
`K_n(ω) ≥ 1/√2 + (√(1 − τ²/4) − τ) · τ/(2√2)`; moreover, when `n ≥ 4`, the estimate is optimal
for `0 ≤ τ ≤ √(2 − √2)`, and in that range equality holds if and only if
`ω = ω_τ = (r, r, s, s, 0, …, 0)`.

**Formalization Note** `n ≥ 2` is the standing assumption of §2 (p.4). "Optimal, equality iff
`ω = ω_τ`" is stated as: `ω_τ ∈ C_n(τ)`, `K_n(ω_τ)` equals the bound, and equality at any
`ω ∈ C_n(τ)` forces `ω = ω_τ` (equality of vectors `Fin n → ℝ`). On `C_n(τ)` one has
`τ² ≤ 2`, so the radicand `1 − τ²/4` is positive. -/
theorem theorem_1 :
    (∀ n : ℕ, 2 ≤ n → ∀ τ : ℝ, ∀ ω ∈ Cn n τ,
      1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ≤ K n ω) ∧
    (∀ n : ℕ, 4 ≤ n → ∀ τ : ℝ, 0 ≤ τ → τ ≤ Real.sqrt (2 - Real.sqrt 2) →
      fourProfile n τ ∈ Cn n τ ∧
      K n (fourProfile n τ) =
        1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ∧
      ∀ ω ∈ Cn n τ,
        K n ω = 1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) →
          ω = fourProfile n τ) := by sorry

end KhintchineTwoRegime
