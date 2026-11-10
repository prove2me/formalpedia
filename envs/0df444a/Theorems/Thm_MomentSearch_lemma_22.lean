-- Prove2me | Theorems.Thm_MomentSearch_lemma_22
-- name    : MomentSearch.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:07.365093+00:00
-- url     : https://prove2.me/theorems/3c232d8f-0509-4474-ac5e-98eda13f950d
-- title:
--   Lemma 22 — affine rescaling preserves vanishing moments
-- statement:
--   Let $n\ge2$, $k\ge0$, and let $\tau_t=\frac{2t}{n-1}-1$ be the scaled grid. For every $a\in\mathbb R^n$ the following are equivalent:
--
--   1. $\sum_{t=0}^{n-1} a_t\, t^i = 0$ for all $i=0,\dots,k$;
--   2. $\sum_{t=0}^{n-1} a_t\, \tau_t^i = 0$ for all $i=0,\dots,k$.
--
--   In particular, two distributions $p,p'$ on $[n]_0$ have the same first $k$ moments ($\mu_i(p)=\mu_i(p')$ for $i=0,\dots,k$) if and only if
--
--   $$
--   \sum_{t=0}^{n-1} p_t\,\tau_t^i=\sum_{t=0}^{n-1} p'_t\,\tau_t^i\qquad\text{for all } i=0,\dots,k.
--   $$
--
--   This lets the moment-matching construction be carried out on the grid in $[-1,1]$, where polynomial inequalities apply.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ indexed by [n]₀ = {0,…,n−1} → functions Fin n → ℝ, the index read as a natural number; reason: Lean convention; same instances
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, Lemma 22, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MomentSearch_moment
import Definitions.Def_MomentSearch_grid

namespace MomentSearch

/-- **Lemma 22** (affine rescaling preserves vanishing moments), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, p.21 (PDF p.23).

For `n ≥ 2`, every `k` and every `a ∈ ℝ^n`: `∑_t a_t t^i = 0` for all `i = 0, …, k` if and only if
`∑_t a_t τ_t^i = 0` for all `i = 0, …, k`. In particular, two distributions `p, p'` on `[n]₀`
have the same first `k` moments iff `∑_t p_t τ_t^i = ∑_t p'_t τ_t^i` for all `i = 0, …, k`.

**Formalization Note.** `τ_t = grid n t`; "the same first `k` moments" means `µ_i(p) = µ_i(p')`
for `i = 0, …, k`; `n ≥ 2` is the paper's standing assumption (§2.1). -/
theorem lemma_22 {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (∀ a : Fin n → ℝ,
      (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * ((t : ℕ) : ℝ) ^ i = 0) ↔
        (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * grid n (t : ℕ) ^ i = 0)) ∧
    (∀ p p' : Fin n → ℝ, p ∈ stdSimplex ℝ (Fin n) → p' ∈ stdSimplex ℝ (Fin n) →
      ((∀ i : ℕ, i ≤ k → moment p i = moment p' i) ↔
        (∀ i : ℕ, i ≤ k →
          ∑ t : Fin n, p t * grid n (t : ℕ) ^ i = ∑ t : Fin n, p' t * grid n (t : ℕ) ^ i))) := by sorry

end MomentSearch
