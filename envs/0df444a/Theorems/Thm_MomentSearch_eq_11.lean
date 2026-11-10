-- Prove2me | Theorems.Thm_MomentSearch_eq_11
-- name    : MomentSearch.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:00.303095+00:00
-- url     : https://prove2.me/theorems/30a283fd-2904-4c17-bcba-9b372a119e34
-- title:
--   Equation (11) — Bernstein's inequality on $[-\rho,\rho]$
-- statement:
--   Let $q$ be a real polynomial with $\deg q\le k$, let $\rho>0$ and $B\in\mathbb R$. If $|q(x)|\le B$ for all $x\in[-\rho,\rho]$, then
--
--   $$
--   |q'(x)|\ \le\ \frac{k\,B}{\sqrt{\rho^2-x^2}}\qquad\text{for all } x\in(-\rho,\rho).
--   $$
--
--   This is Bernstein's inequality (10) applied to $x\mapsto q(\rho x)$; it bounds the derivative of a polynomial in the interior of an interval on which the polynomial is bounded.
--
--   Differences from the source: none.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, Step 4, eq. (11), p.23 (PDF p.25); = eq. (6), p.12 (PDF p.14)

import Mathlib

namespace MomentSearch

/-- **Equation (11)** (scaled Bernstein inequality), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, Step 4, p.23 (PDF p.25);
= eq. (6), p.12 (PDF p.14).

For a real polynomial `q` with `deg q ≤ k` and every `ρ > 0`:
`|q(x)| ≤ B` for all `x ∈ [−ρ, ρ]` implies `|q'(x)| ≤ k B / √(ρ² − x²)` for all `x ∈ (−ρ, ρ)`.

**Formalization Note.** "deg q ≤ k" is `q.natDegree ≤ k`; `q'` is `Polynomial.derivative q`. -/
theorem eq_11 (k : ℕ) (q : Polynomial ℝ) (hq : q.natDegree ≤ k) (ρ B : ℝ) (hρ : 0 < ρ)
    (hB : ∀ x ∈ Set.Icc (-ρ) ρ, |q.eval x| ≤ B) :
    ∀ x ∈ Set.Ioo (-ρ) ρ,
      |(Polynomial.derivative q).eval x| ≤ (k : ℝ) * B / Real.sqrt (ρ ^ 2 - x ^ 2) := by sorry

end MomentSearch
