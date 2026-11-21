-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_equilibrium_multiplier
-- name    : MomentSearch.rakhmanov_equilibrium_multiplier
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:14:58.106931+00:00
-- url     : https://prove2.me/theorems/1ed010ed-a486-4333-9415-b5bea10f6c7b
-- title:
--   Rakhmanov’s equilibrium multiplier on the midpoint grid
-- statement:
--   For $1\le k<N$ and $|x|<r=\sqrt{1-(k/N)^2}$, there are a scale $M>0$, a center $y$, and a polynomial $H$ of degree at most $N-k-1$ with $H(x)\ne0$. They satisfy $\mu'(x)\le M\le N/2$ and $|x-y|\le2/M$, where $\mu'$ is (2.8). For every midpoint node,
--   $$
--   |H(\zeta_j)|\le B|H(x)|\frac{w(x)}{w(\zeta_j)}
--          \frac{1}{\max(1,M|\zeta_j-y|)}
--   $$
--   with an absolute $B>0$ and $w(z)=\exp(V_1(z)-N)$. This isolates the auxiliary polynomial in (2.21). Take $y$ to be a quantile root of the equilibrium polynomial $S$ with intervening mass at most $1/2$, and take $H=S/(X-y)$. Combine the estimates (2.22)–(2.27) with the potential comparison (2.29). The removable quotients at $x=y$ or $\zeta_j=y$ are read using the factored polynomial and the derivative of the phase, so the conclusion uses positive capped denominators throughout.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Ann. of Math. 165 (2007), 55–88. https://annals.math.princeton.edu/2007/165-1/p03 Lemmas 2 and 3 and §2.2, (2.21)–(2.27), (2.29), pp. 64–67.

import Mathlib

theorem MomentSearch.rakhmanov_equilibrium_multiplier :
    ∃ B : ℝ, 0 < B ∧
      ∀ N k : ℕ, 1 ≤ k → k < N →
      let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
      let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
        ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
      ∀ r : ℝ, r = Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2) →
      ∀ x : ℝ, -r < x → x < r →
      ∃ M y : ℝ, ∃ H : Polynomial ℝ,
        0 < M ∧ M ≤ (N : ℝ) / 2 ∧ |x - y| ≤ 2 / M ∧
        (N : ℝ) / Real.pi * Real.arctan ((N : ℝ) / (k : ℝ) *
          Real.sqrt (r ^ 2 - x ^ 2)) ≤ M ∧
        H.natDegree ≤ N - k - 1 ∧ H.eval x ≠ 0 ∧
        (∀ j ∈ Finset.Icc 1 N,
          |H.eval (ζ j)| ≤ B * |H.eval x| * (w x / w (ζ j)) /
            max 1 (M * |ζ j - y|)) := by sorry
