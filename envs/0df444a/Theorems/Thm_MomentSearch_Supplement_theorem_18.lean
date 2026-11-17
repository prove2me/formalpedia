-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_18
-- name    : MomentSearch.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:35:26.319199+00:00
-- url     : https://prove2.me/theorems/a2ee75d9-c5ef-4ffa-8e99-86bdc30f6f3b
-- title:
--   Theorem 18 — moment recovery under bounded atoms: $d_K(\pi,p)=O((Ln/k)\log n)$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $16\le k\le n$ be integers, $L$ a real number, and $\pi$ a distribution on $[n]_0$ with $\|\pi\|_\infty\le L$. Then every distribution $p$ on $[n]_0$ with the same first $k$ moments as $\pi$, i.e. $\mu_i(p)=\mu_i(\pi)$ for $i=0,\dots,k$ where $\mu_i(p)=\sum_t p_t t^i$, satisfies
--   $$d_K(\pi,p)\le C\,\frac{L\,n}{k}\,\log n .$$
--
--   No atom bound is imposed on $p$. The theorem quantifies how small atoms in a nominal distribution limit the CDF ambiguity left by its first $k$ moments, in contrast to the base mission's Theorem 16, where large atoms make moments nearly useless.
--
--   Differences from the source:
--   - encoding: d_K(π, p) = O((L n/k) log n) → ∃ C > 0 chosen before n, k, L, π, p with d_K(π, p) ≤ C·(L n/k)·log₂ n; reason: O(·) hides an absolute constant; the proof's natural log differs from log₂ by a constant factor
--   - encoding: ‖π‖_∞ ≤ L → π_t ≤ L for every t; reason: the entries of π ∈ Δ_n are nonnegative
--   - encoding: the same first k moments → moment p i = moment π i for all i ≤ k (the published MomentSearch.moment, i = 0 included); reason: the base mission's convention; µ₀ = 1 for both distributions
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 18, p.15 (PDF p.17); restated with proof App. C.4, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_MomentSearch_moment
import Definitions.Def_MomentSearch_Supplement_cdf

namespace MomentSearch.Supplement

open MomentSearch

/-- **Theorem 18** (Moment recovery under bounded atoms) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 18, p.15 (PDF p.17);
restated with proof App. C.4, p.31 (PDF p.33)).

There is an absolute constant `C > 0` such that for all integers `16 ≤ k ≤ n`, every real
`L`, every distribution `π` on `[n]₀` with `‖π‖_∞ ≤ L`, and every distribution `p` on `[n]₀`
with the same first `k` moments as `π` (`µ_i(p) = µ_i(π)` for `i = 0, …, k`),
`d_K(π, p) ≤ C · (L n / k) · log n`.

**Formalization Note.** `O(·)` is an absolute constant chosen before `n`, `k`, `L`, `π`, `p`.
`‖π‖_∞ ≤ L` is `π_t ≤ L` for all `t` (the entries are nonnegative). No bound is assumed on the
atoms of `p`. `log` is base 2 (the proof's `ln` differs by a constant factor, absorbed in `C`).
The moments `µ_i` are the published `MomentSearch.moment`. -/
theorem theorem_18 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ), 16 ≤ k → k ≤ n → ∀ L : ℝ,
        ∀ π ∈ stdSimplex ℝ (Fin n), ∀ p ∈ stdSimplex ℝ (Fin n),
          (∀ t, π t ≤ L) → (∀ i : ℕ, i ≤ k → moment p i = moment π i) →
          kolDist π p ≤ C * (L * n / k) * Real.logb 2 n := by sorry

end MomentSearch.Supplement
