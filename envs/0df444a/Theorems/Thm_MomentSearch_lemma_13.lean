-- Prove2me | Theorems.Thm_MomentSearch_lemma_13
-- name    : MomentSearch.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:22.079322+00:00
-- url     : https://prove2.me/theorems/a6a14625-5afe-448f-a9aa-943d87d24bf1
-- title:
--   Lemma 13 — from the grid to the central interval
-- statement:
--   There is an absolute constant $C_1$ such that the following holds. Let $n\ge2$ and let $q$ be a real polynomial with $\deg q\le k\le (n-1)/2$ and $|q(\tau_t)|\le1$ for all $t\in[n]_0$, where $\tau_t=\frac{2t}{n-1}-1$. Then
--
--   $$
--   |q(x)|\le C_1\qquad\text{for all } x\in[-3/4,3/4].
--   $$
--
--   A polynomial of degree at most half the number of grid points that is bounded on the grid stays bounded by an absolute constant on the central part of $[-1,1]$; this is what makes Bernstein's inequality applicable to the dual polynomials of Lemma 12.
--
--   Differences from the source: none.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, Lemma 13, p.12 (PDF p.14); restated App. C.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_MomentSearch_grid

namespace MomentSearch

/-- **Lemma 13** (from the grid to the central interval), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, p.12 (PDF p.14);
restated App. C.1, p.23 (PDF p.25).

Let `q` be a polynomial with `deg q ≤ k ≤ (n − 1)/2` and `|q(τ_t)| ≤ 1` for all `t ∈ [n]₀`.
Then `|q(x)| ≤ C₁` for all `x ∈ [−3/4, 3/4]`, for some absolute constant `C₁`.

**Formalization Note.** The constant is absolute: it is chosen before `n`, `k`, `q` and `x`.
`τ_t = grid n t`; `n ≥ 2` is the standing assumption (§2.1); `k = 0` is allowed, as on the
page (its proof treats `k = 0` separately). -/
theorem lemma_13 :
    ∃ C₁ : ℝ, ∀ n k : ℕ, 2 ≤ n → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
      ∀ q : Polynomial ℝ, q.natDegree ≤ k →
      (∀ t : Fin n, |q.eval (grid n (t : ℕ))| ≤ 1) →
      ∀ x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4), |q.eval x| ≤ C₁ := by sorry

end MomentSearch
