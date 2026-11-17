-- Prove2me | Theorems.Thm_KMeansTaper_Supplement_theorem_3_6
-- name    : KMeansTaper.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:46:07.88471+00:00
-- url     : https://prove2.me/theorems/5cd1ae9e-af08-4b66-ace4-9a785e4c4043
-- title:
--   Theorem 3.6 — LP-optimality for real power costs
-- statement:
--   Let $p\ge1$ be real, let $k\ge2$ be an integer, and let $0\le\ell\le k^2-2k$. There is a finite rational metric $k$-clustering instance with budget $k$ and exactly $k^2$ candidate centers such that every nonempty $S\subseteq F$ with $|S|\le k+\ell$ satisfies
--
--   $$
--   \mathrm{cost}_p(S)\ge
--   \left[1+(3^p-1)\left(1-\frac{k+\ell}{k^2-k}\right)^k\right]\mathrm{LP}_p.
--   $$
--
--   For every natural-valued sequence $\ell(k)=o(k)$, the displayed finite factor converges to
--
--   $$
--   1+\frac{3^p-1}{e};
--   $$
--
--   at $p=2$ it converges to $1+8/e$. Thus the natural squared LP cannot certify a better asymptotic factor even when a lower-order number of extra centers is allowed.
--
--   **Formalization Note** The source's nonnegative integer parameters are represented by natural numbers. The little-$o$ clause uses the standard `atTop` filter. The constructed instance uses the published finite rational metric model, and the power cost and LP specialize exactly to `cost2` and `lp2` at $p=2$.
--
--   Differences from the source:
--   - encoding: integers $k\ge2$ and $0\le\ell\le k^2-2k$ → natural numbers with the same bounds; reason: every source parameter in this range is uniquely a natural number
--   - encoding: the paper assigns infinite cost to $S=\varnothing$ → Lean quantifies over nonempty $S$ because the reused total `nearest` returns zero on the empty set; reason: this excludes only the source's infeasible infinite-cost case
--   - encoding: $\ell=o(k)$ and a factor of $L-o(1)$ → convergence of the explicit factor to $L$ along `atTop`; reason: this is the standard filter meaning of the source's asymptotic notation
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 3.6, p.5 (PDF p.8), proof in Appendix H.3, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_Supplement_powerCost
import Definitions.Def_KMeansTaper_Supplement_lpPower

namespace KMeansTaper
namespace Supplement

open OAI.MetricKMedian (Instance)
open Filter Topology

/-- **Theorem 3.6 (LP-optimality)**, p.5 (PDF p.8).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

For every real `p ≥ 1`, `k ≥ 2`, and `0 ≤ ℓ ≤ k² - 2k`, there is an instance with budget
`k` and exactly `k²` candidate centers on which every nonempty solution using at most `k + ℓ`
centers has power cost at least
`[1 + (3^p - 1)(1 - (k+ℓ)/(k²-k))^k] LP_p`. If `ℓ = o(k)`, this finite factor
converges to `1 + (3^p - 1)/e`; at `p = 2` it converges to `1 + 8/e`.

**Formalization Note.** The source's nonnegative integer parameters are naturals. The paper cost
of the empty facility set is infinite, while the reused total function `nearest` returns zero
there, so `S.Nonempty` excludes only that undefined case. The phrase `ℓ = o(k)` is the standard
filter statement for every natural-valued sequence `ℓ(k)`. -/
theorem theorem_3_6 :
    let factor : ℝ → ℕ → ℕ → ℝ := fun p k ℓ =>
      1 + ((3 : ℝ) ^ p - 1) * (1 - ((k + ℓ : ℕ) : ℝ) / ((k : ℝ) ^ 2 - (k : ℝ))) ^ k
    (∀ p : ℝ, 1 ≤ p → ∀ k ℓ : ℕ, 2 ≤ k → ℓ ≤ k ^ 2 - 2 * k →
      ∃ I : Instance, I.k = k ∧ I.facilities.card = k ^ 2 ∧
        ∀ S : Finset (Fin I.n), S ⊆ I.facilities → S.Nonempty → S.card ≤ k + ℓ →
          powerCost I p S ≥ factor p k ℓ * lpPower I p) ∧
    (∀ p : ℝ, 1 ≤ p → ∀ ℓ : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun k => (ℓ k : ℝ)) (fun k => (k : ℝ)) →
        Tendsto (fun k => factor p k (ℓ k)) atTop
          (nhds (1 + ((3 : ℝ) ^ p - 1) / Real.exp 1))) ∧
    (∀ ℓ : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun k => (ℓ k : ℝ)) (fun k => (k : ℝ)) →
        Tendsto (fun k => factor 2 k (ℓ k)) atTop (nhds (1 + 8 / Real.exp 1))) := by sorry

end Supplement
end KMeansTaper
