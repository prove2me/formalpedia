-- Prove2me | Theorems.Thm_MomentSearch_theorem_24
-- name    : MomentSearch.theorem_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:12.186786+00:00
-- url     : https://prove2.me/theorems/268bbde8-9e39-493f-b5df-4c313258dceb
-- title:
--   Theorem 24 (Rakhmanov) — polynomials bounded on equidistant points
-- statement:
--   For $N\ge1$ let $E_N=\{\zeta_j=-1+(2j-1)/N : j=1,\dots,N\}$ be the set of $N$ equidistant points in $(-1,1)$. There is an absolute constant $C_0$ with the following property. Let $1\le\kappa<N$ be integers and let $Q$ be a real polynomial of degree at most $\kappa$ with $\max_{\zeta\in E_N}|Q(\zeta)|\le1$. Let $r:=\sqrt{1-\kappa^2/N^2}$. Then
--
--   $$
--   |Q(x)|\ \le\ C_0\,\log\frac{\pi}{\arctan\!\bigl(\frac N\kappa\sqrt{r^2-x^2}\bigr)}\qquad\text{for all } x\in(-r,r).
--   $$
--
--   The paper cites this theorem from Rakhmanov (Ann. Math. 165 (2007), Theorem 1) and uses it to pass from a bound on a grid to a bound on the central part of the interval, without the restriction $k=O(\sqrt n)$ that Markov's inequality would impose.
--
--   **Formalization Note** The constant is chosen before $N$, $\kappa$, $Q$ and $x$. The logarithm is base 2.
--
--   Differences from the source:
--   - encoding: κ < N (κ a natural number) → 1 ≤ κ < N; reason: N/κ is undefined at κ = 0 (Lean would read it as 0); the paper applies the theorem only with κ = k ≥ 1, and Rakhmanov's original assumes degree n ≥ 1
--   - encoding: log (the paper's standing convention: base 2) → Real.logb 2; reason: base 2 per §2.1; since C₀ is existential any fixed base gives an equivalent statement
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, Theorem 24 (Rakhmanov [Rak07, Theorem 1]), p.23 (PDF p.25)

import Mathlib

namespace MomentSearch

/-- **Theorem 24** (Rakhmanov [Rak07, Theorem 1]), as stated in Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, p.23 (PDF p.25).

Let `E_N = {ζ_j = −1 + (2j − 1)/N : j = 1, …, N}` be the set of `N` equidistant points in
`(−1, 1)`, let `κ < N`, and let `Q` be a polynomial of degree at most `κ` with
`max_{ζ∈E_N} |Q(ζ)| ≤ 1`. Let `r := √(1 − κ²/N²)`. Then there is an absolute constant `C₀` with
`|Q(x)| ≤ C₀ log (π / arctan((N/κ)√(r² − x²)))` for all `x ∈ (−r, r)`.

**Formalization Note.** The constant is absolute: it is chosen before `N`, `κ`, `Q` and `x`.
`κ ≥ 1` is required because `N/κ` is undefined at `κ = 0` (Lean would read it as `0`); the
paper applies the theorem only with `κ = k ≥ 1`. The logarithm is base 2 (the paper's standing
convention, §2.1); since `C₀` is existential any fixed base gives an equivalent statement. -/
theorem theorem_24 :
    ∃ C₀ : ℝ, ∀ N κ : ℕ, 1 ≤ κ → κ < N →
      ∀ Q : Polynomial ℝ, Q.natDegree ≤ κ →
      (∀ j : ℕ, 1 ≤ j → j ≤ N → |Q.eval (-1 + (2 * (j : ℝ) - 1) / (N : ℝ))| ≤ 1) →
      ∀ r : ℝ, r = Real.sqrt (1 - (κ : ℝ) ^ 2 / (N : ℝ) ^ 2) →
      ∀ x : ℝ, -r < x → x < r →
        |Q.eval x| ≤
          C₀ * Real.logb 2
            (Real.pi / Real.arctan ((N : ℝ) / (κ : ℝ) * Real.sqrt (r ^ 2 - x ^ 2))) := by sorry

end MomentSearch
