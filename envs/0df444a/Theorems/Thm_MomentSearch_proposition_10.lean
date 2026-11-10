-- Prove2me | Theorems.Thm_MomentSearch_proposition_10
-- name    : MomentSearch.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:05.695386+00:00
-- url     : https://prove2.me/theorems/4d10554a-138c-45cd-ade1-7edfe54de1d8
-- title:
--   Proposition 10 — two distributions with matching moments and separated peaks
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $n\ge3$ and $1\le k\le(n-1)/2$ be integers. For any two integers $m,m_0\in\bigl[\frac{n-1}4,\frac{3(n-1)}4\bigr]$ there exist two distributions $p,p'$ on $[n]_0$ and a value
--
--   $$
--   \gamma\ \le\ C\,\frac{k}{n-1}\,|m-m_0|
--   $$
--
--   such that $p_m\ge1-\gamma$, $p'_{m_0}\ge1-\gamma$, and $\mu_i(p)=\mu_i(p')$ for all $i=0,\dots,k$.
--
--   Matching the first $k$ moments therefore does not determine where most of the mass lies: peaks at distance of order $n/k$ are compatible with the same moments.
--
--   Differences from the source:
--   - encoding: integers m, m₀ ∈ [(n−1)/4, 3(n−1)/4] → m m₀ : Fin n with the same real bounds; reason: every integer in that interval lies in [n]₀, so no instance changes
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, Proposition 10, p.10 (PDF p.12); restated App. C.1, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_MomentSearch_moment

namespace MomentSearch

/-- **Proposition 10** (two distributions with matching moments and separated peaks), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…),
§4.1, p.10 (PDF p.12); restated App. C.1, pp.19–20 (PDF pp.21–22).

There is an absolute constant `C > 0` such that the following holds. Let `n ≥ 3` and
`1 ≤ k ≤ (n − 1)/2` be integers. For any two integers `m, m₀ ∈ [(n−1)/4, 3(n−1)/4]`, there
exist two distributions `p, p'` on `[n]₀` and a value `γ ≤ C (k/(n−1)) |m − m₀|` such that
`p_m, p'_{m₀} ≥ 1 − γ` and `µ_i(p) = µ_i(p')` for all `i = 0, …, k`.

**Formalization Note.** `m, m₀` are elements of `Fin n`: every integer of
`[(n−1)/4, 3(n−1)/4]` lies in `[n]₀`, so this changes no instance. -/
theorem proposition_10 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 3 ≤ n → 1 ≤ k → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
      ∀ m m₀ : Fin n,
        ((n : ℝ) - 1) / 4 ≤ ((m : ℕ) : ℝ) → ((m : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
        ((n : ℝ) - 1) / 4 ≤ ((m₀ : ℕ) : ℝ) → ((m₀ : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
        ∃ p p' : Fin n → ℝ, ∃ γ : ℝ,
          p ∈ stdSimplex ℝ (Fin n) ∧ p' ∈ stdSimplex ℝ (Fin n) ∧
          γ ≤ C * ((k : ℝ) / ((n : ℝ) - 1)) * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| ∧
          1 - γ ≤ p m ∧ 1 - γ ≤ p' m₀ ∧
          ∀ i : ℕ, i ≤ k → moment p i = moment p' i := by sorry

end MomentSearch
