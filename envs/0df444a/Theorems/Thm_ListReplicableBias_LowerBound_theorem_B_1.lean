-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_theorem_B_1
-- name    : ListReplicableBias.LowerBound.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:56.406907+00:00
-- url     : https://prove2.me/theorems/f00176f8-b43a-47d7-9146-a22d0446e46a
-- title:
--   Theorem B.1 (= Theorem 5.7) — Uniform adaptive sample lower bound
-- statement:
--   There exist an absolute constant $c>0$ and a dimension threshold $d_0\in\mathbb N$ such that for every $d\ge d_0$, every $0<\varepsilon,\delta<1/8$, and every randomized adaptive $N$-toss sampling algorithm $A$ that is $(d+1,\varepsilon,\delta)$-list replicable,
--   $$N\ge c\,\frac{d^2}{\varepsilon^2\ln d}.$$
--   Both $c$ and $d_0$ are independent of $\varepsilon,\delta,N$ and $A$. The theorem covers arbitrary probability spaces for internal randomness and coin choices depending on the entire preceding history. This is the full-strength headline lower bound, rather than its fixed-allocation special case.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - encoding: arbitrary randomized adaptive sampling algorithms and full histories → an arbitrary probability seed space, prefix-dependent coin choices, and the explicit transcript density; failure is `none`; reason: all private randomness is included in the seed, earlier choices are recoverable from it and earlier outcomes, and ignored tosses pad a fixed cap without changing the output law
--   - generalization: epsilon and delta fixed before the asymptotic lower bound → one positive constant and one dimension threshold chosen before all accuracy and failure parameters; reason: the explicit estimate in Appendix B gives an epsilon- and delta-independent threshold and supports c=3/25600
--   - encoding: log d in the asymptotic denominator → Real.log of the real cast of d; reason: this is the natural logarithm used by the proof; the existential threshold may be at least 3
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem B.1 (= Theorem 5.7), PDF p. 14

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Theorem B.1 (= Theorem 5.7), PDF p. 14. Constants and the dimension
threshold are uniform over accuracy, failure probability, horizon and algorithm,
as supported by the explicit estimate on PDF p. 15. -/
theorem theorem_B_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ ε δ : ℝ, ε ∈ Set.Ioo (0 : ℝ) (1 / 8) → δ ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      ∀ (N : ℕ) (A : SamplingAlgorithm d N), IsListReplicable A (d + 1) ε δ →
        c * (d : ℝ) ^ 2 / (ε ^ 2 * Real.log (d : ℝ)) ≤ (N : ℝ) := by sorry

end ListReplicableBias.LowerBound
