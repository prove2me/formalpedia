-- Prove2me | Theorems.Thm_GradSuffice_eq_18
-- name    : GradSuffice.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:16.170443+00:00
-- url     : https://prove2.me/theorems/73994b3a-b102-4c94-9d9a-4821961fefcd
-- title:
--   Eq. (18), p.25 — $\gamma(m^n)\le\gamma(m)^n$ and $\gamma$ is nonincreasing
-- statement:
--   Let $X$ be a Banach space and let $\gamma(m)$ be the smallest constant such that every martingale $(\xi_1,\dots,\xi_m)$ of size $m$ in $X^\star$ satisfies
--   $$\sqrt{\mathbb E\Big\|\frac1m\sum_{i=1}^m\xi_i\Big\|_\star^2}\le\gamma(m)\sup_i\sqrt{\mathbb E\|\xi_i\|_\star^2}.\tag{17}$$
--
--   **Eq. (18) and monotonicity.**
--   1. For every $m\ge1$ and every $n$,
--   $$\gamma(m^n)\le\gamma(m)^n .\tag{18}$$
--   2. $\gamma$ is nonincreasing: $\gamma(M)\le\gamma(k)$ whenever $1\le k\le M$.
--
--   Together these are the boosting step in the proof of Lemma 3: a value of $\gamma$ close to $1$ at a large size forces values close to $1$ at all smaller sizes.
--
--   Differences from the source:
--   - reading: martingale of size m (not necessarily binary) → finitely supported martingale-difference law in X⋆ (conditional mean zero given the sequence's own past); reason: §6.1 defines the martingales of the paper as finitely supported
--   - encoding: γ(m), the infimal upper bound in (17) → sInf of the nonnegative constants for which (17) holds for every such law; reason: equal to the paper's infimum when X ≠ 0; avoids the junk sInf of a set unbounded below when X = 0
--   - encoding: "for every n"; sizes m, k, M → n ∈ ℕ (including 0), sizes ≥ 1; reason: sizes of martingales are positive; at n = 0 the claim is γ(1) ≤ 1
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §8, Eq. (18) and the monotonicity of γ, p.25

import Mathlib
import Definitions.Def_GradSuffice_gammaConst

namespace GradSuffice

/-- **Eq. (18) and monotonicity of `γ`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §8, p.25: "We want to show that for every `n`:
`γ(mⁿ) ≤ γ(m)ⁿ`. (18)" and "We also use that `γ(m)` is nonincreasing in `m`. Indeed, for `M ≥ k`,
[…] this gives `γ(M) ≤ γ(k)`."

**Formalization Note.** `γ` is `gammaConst X`, defined through finitely supported
martingale-difference laws in `X⋆` (Eq. (17), p.24). Sizes are at least `1`. -/
theorem eq_18 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
    (∀ m n : ℕ, 1 ≤ m → gammaConst X (m ^ n) ≤ gammaConst X m ^ n) ∧
      (∀ k M : ℕ, 1 ≤ k → k ≤ M → gammaConst X M ≤ gammaConst X k) := by sorry

end GradSuffice
