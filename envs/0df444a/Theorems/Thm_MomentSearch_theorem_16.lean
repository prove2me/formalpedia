-- Prove2me | Theorems.Thm_MomentSearch_theorem_16
-- name    : MomentSearch.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:57.014496+00:00
-- url     : https://prove2.me/theorems/325ce330-24ff-485a-9444-3953d2f86482
-- title:
--   Theorem 16 — exact moments can be useless for search: $\alpha(\mathcal U_{\sigma_k})=\Omega(\log\frac{n}{k\log n})$
-- statement:
--   Let $\mathcal U_{\sigma_k}$ be the uncertainty collection of the $k$-moment sketch $\sigma_k(p)=(\mu_0(p),\dots,\mu_k(p))$ on $[n]_0$, and let $\alpha$ denote the approximability factor. Logarithms are base 2.
--
--   1. There is an absolute constant $C'>0$ such that, for all sufficiently large $n$ and every integer $1\le k\le n/(C'\log n)$,
--   $$
--   \alpha(\mathcal U_{\sigma_k})=\Omega\Bigl(\log\frac{n}{k\log n}\Bigr),
--   $$
--   i.e. there are $c>0$ and $N$ with $\alpha(\mathcal U_{\sigma_k})\ge c\log\frac{n}{k\log n}$ for all $n\ge N$ and all such $k$.
--   2. In particular, the bound is $\Omega(\log\frac nk)$ for $k\le n/\log^2 n$: there are $c_2>0$ and $N_2$ with $\alpha(\mathcal U_{\sigma_k})\ge c_2\log\frac nk$ for all $n\ge N_2$ and $1\le k\le n/\log^2n$.
--   3. And it is $\Omega(\log n)$ for $k\le n^{1-\delta}$ with constant $\delta\in(0,1]$: for every such $\delta$ there are $c_3>0$ and $N_3$ with $\alpha(\mathcal U_{\sigma_k})\ge c_3\log n$ for all $n\ge N_3$ and $1\le k\le n^{1-\delta}$.
--
--   Binary search achieves $O(\log n)$ with no information at all, so even $n^{1-\delta}$ exact moments do not allow a better worst-case guarantee than ignoring them.
--
--   Differences from the source:
--   - encoding: Ω(·) for all sufficiently large n → ∃ c > 0, ∃ N, ∀ n ≥ N (c and N chosen after C′; in clause 3 after δ); reason: standard reading of Ω with a threshold
--   - encoding: α(𝒰) ≥ b for a real b → ENNReal.ofReal b ≤ α(𝒰), α valued in [0, ∞]; reason: for b ≥ 0 the two are equivalent; for b < 0 both are trivially true (α ≥ 0), so no instance changes
--   - reading: In particular, the bound is Ω(log n/k) for k ≤ n/log² n, and Ω(log n) for k ≤ n^{1−δ} → two further conjuncts, each with its own constant and threshold, over its own range of k; reason: the sentence is part of the theorem statement on p.13 and p.26; its ranges are stated without the C′ restriction
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.2, Theorem 16, p.13 (PDF p.15); restated App. C.3, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_sketchCollection
import Definitions.Def_MomentSearch_moment

open scoped ENNReal

namespace MomentSearch

/-- **Theorem 16** (exact moments can be useless for search), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.2, p.13 (PDF p.15);
restated App. C.3, p.26 (PDF p.28).

"There is an absolute constant C′ > 0 such that, for all sufficiently large n and every integer
1 ≤ k ≤ n/(C′ log n), the uncertainty collection U_{σ_k} induced by the moment sketch
σ_k(p) := (µ_0(p), …, µ_k(p)) satisfies α(U_{σ_k}) = Ω(log (n/(k log n))). In particular, the bound
is Ω(log (n/k)) for k ≤ n/log² n, and Ω(log n) for k ≤ n^{1−δ} with constant δ ∈ (0, 1]."

**Formalization Note.** Three conjuncts: the main bound and the two "In particular" clauses.
`Ω` with "sufficiently large n" is: a constant `c > 0` and a threshold `N` with the bound for all
`n ≥ N`; `C′` comes first, `c` and `N` may depend on it; in the third clause `c₃, N₃` may depend
on `δ` ("with constant δ"). Logarithms are base 2 (§2.1). `α` is `approxFactor` (in `ℝ≥0∞`),
and a real lower bound `b` is compared as `ENNReal.ofReal b ≤ α`, which for `b ≥ 0` is `b ≤ α`. -/
theorem theorem_16 :
    (∃ C' : ℝ, 0 < C' ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ (n : ℝ) / (C' * Real.logb 2 n) →
      ENNReal.ofReal (c * Real.logb 2 ((n : ℝ) / ((k : ℝ) * Real.logb 2 n))) ≤
        approxFactor (sketchCollection (momentSketch n k))) ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ (n : ℝ) / Real.logb 2 n ^ 2 →
      ENNReal.ofReal (c₂ * Real.logb 2 ((n : ℝ) / (k : ℝ))) ≤
        approxFactor (sketchCollection (momentSketch n k))) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ N₃ : ℕ, ∀ n : ℕ, N₃ ≤ n → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ (n : ℝ) ^ (1 - δ) →
      ENNReal.ofReal (c₃ * Real.logb 2 n) ≤
        approxFactor (sketchCollection (momentSketch n k))) := by sorry

end MomentSearch
