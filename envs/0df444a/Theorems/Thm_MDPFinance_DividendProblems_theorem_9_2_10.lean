-- Prove2me | Theorems.Thm_MDPFinance_DividendProblems_theorem_9_2_10
-- name    : MDPFinance.DividendProblems.theorem_9_2_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:13:42.55584+00:00
-- url     : https://prove2.me/theorems/f4bd54d5-8e3a-4788-905f-a60a0a13ea36
-- title:
--   Theorem 9.2.10 — bounded wave lengths and the barrier-policy special case
-- statement:
--   Two refinements of the goal under an extra hypothesis on how negative the reserve's increments can be: if the reserve can never drop by more than $z_0$ in one period, every wave of the optimal band-policy has length at most $z_0$ (part a); if it can never drop by more than $1$, the band-policy collapses all the way to a single barrier-policy (part b) — the general result cannot be improved further without an extra hypothesis of this kind, since §9.2's own Figures 9.1-9.2 (not numbered results) show genuine multi-wave optimal policies occur without it.
--
--   **Moderation note.** `z₀ ∈ ℕ` is now positive as in the book, probabilities are compared in `[0,∞]`; otherwise as drafted (wave length `d_k − c_{k−1}`, the definition's, is what the proof bounds — the theorem's display `c_{k+1} − d_k` is the book's typo).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 279, PDF 289, Theorem 9.2.10

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend
import Definitions.Def_MDPFinance_DividendProblems_BandPolicy

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Theorem 9.2.10 (Bäuerle–Rieder, p. 279, PDF 289). a) If `\mathbb P(Z \ge -z_0) = 1` for some
`z_0 \in \mathbb N`, then the length of the waves of `f^*` is bounded by `z_0`: `f^*` has a
band-policy parametrization `(n,c,d)` (Definition 9.2.5) with every wave length `d_k - c_{k-1}
\le z_0`. b) If `\mathbb P(Z \ge -1) = 1` then `(f^*,f^*,\dots)` is a barrier-policy. -/
theorem theorem_9_2_10 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ z0 : ℕ, 0 < z0 → M.Zpmf.toMeasure {k : ℤ | -(z0 : ℤ) ≤ k} = 1 →
        ∃ n : ℕ, ∃ c d : ℕ → ℕ,
          ((∀ k, 1 ≤ k → k ≤ n → d k - c (k - 1) ≥ 2) ∧ c 0 < d 1 ∧
              (∀ k, 1 ≤ k → k < n → c k < d (k + 1)) ∧ (∀ k, 1 ≤ k → k ≤ n → d k ≤ c k) ∧
              (∀ x, x ≤ c 0 → fstar (x : ℤ) = 0) ∧
              (∀ k, k < n → ∀ x, c k < x → x < d (k + 1) → fstar (x : ℤ) = x - c k) ∧
              (∀ k, 1 ≤ k → k ≤ n → ∀ x, d k ≤ x → x ≤ c k → fstar (x : ℤ) = 0) ∧
              ∀ x, c n < x → fstar (x : ℤ) = x - c n) ∧
            ∀ k, 1 ≤ k → k ≤ n → waveLength c d k ≤ z0) ∧
      (M.Zpmf.toMeasure {k : ℤ | -1 ≤ k} = 1 →
        IsBarrierPolicy (fun x : ℕ => fstar (x : ℤ))) := by sorry

end MDPFinance.DividendProblems
