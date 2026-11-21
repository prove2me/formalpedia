-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_9
-- name    : MomentSearch.Supplement.theorem_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T09:34:45.2422+00:00
-- url     : https://prove2.me/theorems/10db2c3b-6c32-4993-9ccb-33a9898ad103
-- title:
--   Theorem 9 — $\alpha(\mathcal U_{K,\delta})=\Theta(\log n/\log(1/\delta))$ for $1/n\le\delta\le1/2$
-- statement:
--   There are absolute constants $c,C>0$ such that the following hold.
--
--   1. For every $n\ge2$ and $1/n\le\delta\le1/2$,
--   $$c\,\frac{\log n}{\log(1/\delta)}\le\alpha(\mathcal U_{K,\delta})\le C\,\frac{\log n}{\log(1/\delta)}.$$
--   2. In particular, for $\varepsilon\in(0,1]$ and $n\ge 2^{1/\varepsilon}$, balls of radius $n^{-\varepsilon}$ satisfy $c/\varepsilon\le\alpha(\mathcal U_{K,n^{-\varepsilon}})\le C/\varepsilon$.
--   3. By monotonicity, the lower bound also holds for larger radii: for $\varepsilon\in(0,1]$, $n\ge2^{1/\varepsilon}$ and every $\delta\ge n^{-\varepsilon}$, $\alpha(\mathcal U_{K,\delta})\ge c/\varepsilon$.
--
--   Here $\mathcal U_{K,\delta}$ is the collection of all Kolmogorov balls of radius $\delta$ around distributions in $\Delta_n$. The theorem determines, up to constants, how the approximability of Kolmogorov balls depends on their radius.
--
--   Differences from the source:
--   - encoding: α(𝒰_{K,δ}) = Θ(log n / log(1/δ)), and Θ(1/ε) in the 'in particular' clause → ∃ c, C > 0, chosen before n, δ, ε and shared by the three clauses; both bounds compared through ENNReal.ofReal; logarithms base 2; reason: Θ hides absolute constants; log n / log(1/δ) is base-independent and equals 1/ε at δ = n^{−ε}, so the same constants serve all clauses
--   - reading: by monotonicity, the lower bound also holds for larger radii → for ε ∈ (0, 1], n ≥ 2^{1/ε} and every δ ≥ n^{−ε}: c/ε ≤ α(𝒰_{K,δ}); reason: the 'lower bound' of the preceding sentence is c/ε under the same conditions on ε and n
--   - encoding: n ≥ 2^{1/ε} (clauses 2 and 3) → n ≥ 2 and (2:ℝ)^{1/ε} ≤ n; reason: n ≥ 2^{1/ε} ≥ 2 already; the extra hypothesis excludes nothing
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 9, p.9 (PDF p.11); restated App. B.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_Supplement_cdf

open scoped ENNReal

namespace MomentSearch.Supplement

open MomentSearch

/-- **Theorem 9** (Approximability of Kolmogorov balls) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 9, p.9 (PDF p.11);
restated App. B.2, p.18 (PDF p.20)).

There are absolute constants `0 < c` and `0 < C` such that:
1. for every `n ≥ 2` and `1/n ≤ δ ≤ 1/2`,
   `c · log n / log(1/δ) ≤ α(𝒰_{K,δ}) ≤ C · log n / log(1/δ)`;
2. (in particular) for `ε ∈ (0, 1]` and `n ≥ 2^{1/ε}`, `c/ε ≤ α(𝒰_{K,n^{−ε}}) ≤ C/ε`;
3. (by monotonicity) for `ε ∈ (0, 1]`, `n ≥ 2^{1/ε}` and every radius `δ ≥ n^{−ε}`,
   `α(𝒰_{K,δ}) ≥ c/ε`.

**Formalization Note.** `Θ(·)` is the pair of absolute constants `c, C`, shared by the three
clauses. Lower and upper bounds are compared through `ENNReal.ofReal`. `log` is base 2 (the
ratio is base-independent). -/
theorem theorem_9 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ δ : ℝ, 1 / (n : ℝ) ≤ δ → δ ≤ 1 / 2 →
        ENNReal.ofReal (c * Real.logb 2 n / Real.logb 2 (1 / δ)) ≤ approxFactor (kolCollection n δ) ∧
        approxFactor (kolCollection n δ) ≤ ENNReal.ofReal (C * Real.logb 2 n / Real.logb 2 (1 / δ))) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (n : ℕ), 2 ≤ n → (2 : ℝ) ^ (1 / ε) ≤ n →
        ENNReal.ofReal (c / ε) ≤ approxFactor (kolCollection n ((n : ℝ) ^ (-ε))) ∧
        approxFactor (kolCollection n ((n : ℝ) ^ (-ε))) ≤ ENNReal.ofReal (C / ε)) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (n : ℕ), 2 ≤ n → (2 : ℝ) ^ (1 / ε) ≤ n →
        ∀ δ : ℝ, (n : ℝ) ^ (-ε) ≤ δ →
          ENNReal.ofReal (c / ε) ≤ approxFactor (kolCollection n δ)) := by sorry

end MomentSearch.Supplement
