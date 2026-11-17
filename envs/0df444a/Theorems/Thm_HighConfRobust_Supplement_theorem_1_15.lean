-- Prove2me | Theorems.Thm_HighConfRobust_Supplement_theorem_1_15
-- name    : HighConfRobust.Supplement.theorem_1_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:43:43.473727+00:00
-- url     : https://prove2.me/theorems/7f4916dd-e610-4982-b774-d481e32c3d4a
-- title:
--   Theorem 1.15 — a high-confidence algorithm on $n$ samples yields an $(\varepsilon, C(2C+1)\alpha, \beta^{1/2}, \mathcal F)$-robust algorithm on $2n$ samples
-- statement:
--   Consider a statistical task on a sample space $\mathcal X$ with output space $\mathcal Y$, parameter map $\theta$ and a loss $\mathrm{loss}:\mathcal Y\times\mathcal Y\to\mathbb R_{\ge0}$ that is symmetric and satisfies the approximate triangle inequality
--
--   $$
--   \mathrm{loss}(y_1,y_2)\le C\big(\mathrm{loss}(y_1,y_3)+\mathrm{loss}(y_3,y_2)\big)\qquad(C\ge1).
--   $$
--
--   Let $\mathcal F$ be a family of distributions and let $A$ be a randomized algorithm on $n$ samples that is $(\alpha,\beta,\mathcal F)$-high-confidence. Then there is a single randomized algorithm $A'$ on $2n$ samples that, for every $\varepsilon$ with
--
--   $$
--   0<\varepsilon<\min\Big(\frac{\log(1/\beta)}{32n},\ \frac14\Big),
--   $$
--
--   is
--
--   $$
--   \big(\varepsilon,\ C(2C+1)\,\alpha,\ \beta^{1/2},\ \mathcal F\big)\text{-robust}
--   $$
--
--   against adaptive $\varepsilon$-adversaries: for every $D\in\mathcal F$ and every adaptive $\varepsilon$-adversary $T$, with probability at least $1-\sqrt\beta$ over $S\sim D^{\otimes 2n}$ and the randomness of $T$ and $A'$, $\mathrm{loss}(A'(T(S)),\theta(D))\le C(2C+1)\alpha$.
--
--   High-confidence estimation therefore implies robustness to strong contamination on the same distribution family, at the price of doubling the sample size and losing computational efficiency.
--
--   **Formalization Note** $A$ is a jointly measurable map with a seed law, and the loss is measurable as a function on $\mathcal Y\times\mathcal Y$. The algorithm $A'$ (its seed space, seed law and map) is chosen once, before $\varepsilon$, $D$ and the adversary, as the page's "there exists another algorithm $A'$ that is … -robust for any $0<\varepsilon<\dots$" reads, and it is jointly measurable in the corrupted dataset and its seed.
--
--   Differences from the source:
--   - reading: error O(α), with the constants of ≲ hidden (p.4) → error C(2C+1)α, C ≥ 1 the constant of the loss's approximate triangle inequality; reason: the explicit value of the proof (Lemma 5.5, pp.22–23: clean evaluations are pairwise within 2Cα, the chosen index set has diameter at most 2Cα, and the output is within C(2Cα + α) of θ(D)); it implies the O-statement
--   - encoding: loss(y1, y2) ≲ loss(y1, y3) + loss(y3, y2), loss : Y × Y → R+ symmetric → hypotheses 0 ≤ loss, symmetry, loss y₁ y₂ ≤ C (loss y₁ y₃ + loss y₃ y₂) with 1 ≤ C; reason: a C-triangle inequality holds with max(C, 1); no loss is excluded
--   - encoding: 0 < ε < min(log(1/β)/(32n), 1/4) → 0 < ε, ε < 1/4, 0 ≤ β and β < exp(−32nε); reason: equivalent for β > 0 and n ≥ 1; at β = 0 (bound +∞) every ε < 1/4 is allowed, which Lean's log 0 = 0 would wrongly forbid; at n = 0, where the page divides by 0, it asks β < 1
--   - encoding: algorithm A with randomness, loss : Y × Y → R+, probabilities of events → A : (Fin n → X) → Ω → Y with Measurable (uncurry A), seed law ν, Measurable (uncurry loss); failure-set measure bounds; reason: the standing convention that algorithms and the loss (a function on Y × Y) are measurable, so the success events of A and of the constructed A′ are events
--   - encoding: adaptive ε-adversary, a (randomized) algorithm whose output overlaps S in at least (1 − ε)n elements, reorderable → a jointly measurable T with a probability seed law on a measurable space in the universe of X, with a permutation matching at least (1 − ε)m positions for every input and seed; reason: multiset overlap of size k is a permutation matching k positions; adversaries are algorithms, measurable by the standing convention
--   - encoding: there exists another algorithm A′ → there exist a seed space Ω′ (in the universe of Ω), a probability seed law and a jointly measurable map A′ : (Fin (2n) → X) → Ω′ → Y; reason: algorithms are measurable by the standing convention; the construction of the proof (a uniform permutation, finitely many evaluations of A, loss comparisons) is measurable under the hypotheses
--   - encoding: θ : F → Y → θ : ProbabilityMeasure X → Y; reason: only the values on F enter the statement
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Theorem 1.15, p.23 (first stated p.9; Definitions 1.1, 1.3, 1.5, pp.4–5)

import Mathlib
import Definitions.Def_HighConfRobust_IsHighConfidence
import Definitions.Def_HighConfRobust_Supplement_IsAdaptiveAdversary
import Definitions.Def_HighConfRobust_Supplement_IsAdaptiveRobust

namespace HighConfRobust.Supplement

universe u v

open MeasureTheory

/-- **Theorem 1.15** (strong contamination, p.23; first stated p.9). Consider a statistical task
with a nonnegative, symmetric loss satisfying `loss(y₁, y₂) ≤ C (loss(y₁, y₃) + loss(y₃, y₂))`. If
`A` is `(α, β, F)`-high-confidence on `n` samples, then there is an algorithm `A'` on `2n` samples
that is `(ε, C(2C + 1)α, β^{1/2}, F)`-robust against adaptive `ε`-adversaries for every `ε` with
`0 < ε < min(log(1/β)/(32n), 1/4)`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Theorem 1.15, p.23 (also p.9; Definitions 1.1, 1.3, 1.5, pp.4–5).

**Formalization Note**
* The error `O(α)` is the explicit `C(2C + 1)α` of the proof (Lemma 5.5 and p.23): the clean
  evaluations are pairwise within `2Cα`, the chosen index set has diameter at most that, and the
  output is within `C(2Cα + α)` of `θ(D)` through a clean evaluation. `C ≥ 1` is the constant of
  the loss's `≲` (p.4).
* `ε < log(1/β)/(32n)` is written `β < exp(−32nε)` with `0 ≤ β`: the same condition for `β > 0` and
  `n ≥ 1`; at `β = 0` (bound `+∞`) every `ε < 1/4` is allowed.
* `A'` (its seed space, seed law and map) is chosen once, before `ε`, `D` and the adversary, as
  the page's "there exists another algorithm `A'` that is … -robust for any `0 < ε < …`" reads:
  one `A'` for every admissible `ε` (the proof's `r = ⌊2nε⌋` may be replaced by the largest integer
  below `2n·min(log(1/β)/(32n), 1/4)`, which covers every admissible `ε` with the same failure
  bound). `A'` is required to be jointly measurable in the corrupted dataset and its seed.
* `A` is jointly measurable with seed law `ν`, and the loss is measurable as a function on
  `Y × Y` (the page's `loss : Y × Y → ℝ₊`): the standing convention that algorithms and losses are
  measurable, so that the constructed algorithm (finitely many evaluations of `A`, loss comparisons)
  is itself measurable and its failure events are events. -/
theorem theorem_1_15 {X : Type u} {Y : Type*} {Ω : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
    (loss : Y → Y → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hloss_nonneg : ∀ y y', 0 ≤ loss y y') (hloss_symm : ∀ y y', loss y y' = loss y' y)
    (hloss_tri : ∀ y₁ y₂ y₃, loss y₁ y₂ ≤ C * (loss y₁ y₃ + loss y₃ y₂))
    (hloss_meas : Measurable (Function.uncurry loss))
    (F : Set (ProbabilityMeasure X)) (θ : ProbabilityMeasure X → Y) (α β : ℝ) (n : ℕ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A : (Fin n → X) → Ω → Y)
    (hA : Measurable (Function.uncurry A))
    (hHC : HighConfRobust.IsHighConfidence loss θ A ν α β F) (hβ : 0 ≤ β) :
    ∃ (Ω' : Type v) (_ : MeasurableSpace Ω') (ν' : Measure Ω') (_ : IsProbabilityMeasure ν')
      (A' : (Fin (2 * n) → X) → Ω' → Y),
      Measurable (Function.uncurry A') ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → β < Real.exp (-(32 * n * ε)) →
        IsAdaptiveRobust loss θ A' ν' ε (C * (2 * C + 1) * α) (Real.sqrt β) F := by sorry

end HighConfRobust.Supplement
