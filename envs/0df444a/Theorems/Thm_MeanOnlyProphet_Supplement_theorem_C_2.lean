-- Prove2me | Theorems.Thm_MeanOnlyProphet_Supplement_theorem_C_2
-- name    : MeanOnlyProphet.Supplement.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:29:51.74005+00:00
-- url     : https://prove2.me/theorems/958650ac-27d9-471a-a319-346e2f2ef58b
-- title:
--   Theorem C.2 — no randomized adaptive algorithm reaches $\beta^*-\varepsilon$ on two normalized i.i.d. inputs
-- statement:
--   Let $D>0$ be the solution of the Hill–Kertz equation
--   $$
--   \int_0^1\frac{dy}{D+y-y\log y}=1\qquad(0\cdot\log0=0),
--   $$
--   and let $\beta^*=1/(1+D)\approx0.7454$ be the optimal full-information ratio for i.i.d. prophet inequalities. There are a constant $\varepsilon>0$ and an $n_0$ with the following property. For every $n\ge n_0$ there are two laws $F_{0,n},F_{1,n}$ of nonnegative values with finite mean and $\mathbb E[X^*]=1$ for $n$ i.i.d. draws, such that every randomized, history-dependent online algorithm $A$ for $n$ values satisfies
--   $$
--   \min\big\{\mathbb E_{F_{0,n}}[\mathrm{ALG}_A],\ \mathbb E_{F_{1,n}}[\mathrm{ALG}_A]\big\}\ \le\ \beta^*-\varepsilon.
--   $$
--   The pair does not depend on $A$. So an algorithm that knows only $n$ and $\mathbb E[X^*]$ cannot match the full-information ratio $\beta^*$, even if it is told the two candidate laws.
--
--   **Formalization Note** An algorithm has an arbitrary seed space with an arbitrary probability law. It is given by measurable, non-anticipating stopping sets (`HistAlg`).
--
--   Differences from the source:
--   - encoding: β* defined by (C.1) → a hypothesis on D > 0 with the integral equal to 1, and β* = 1/(1 + D); reason: (C.1) has exactly one solution D > 0 (published CorreaThreshold.Adaptive.beta_star_existsUnique with β = 1 + D), so the hypothesis pins β* and is satisfiable; Lean's log 0 = 0 matches 0 · log 0 = 0
--   - encoding: randomized, history-dependent algorithm → a seed probability space (any Ω : Type, any probability law) and measurable stopping sets whose membership at arrival i depends only on the seed and the first i values; reward 0 if it never stops; reason: this is the §2/App. C.1 model; measurability makes ALG_A a random variable
--   - encoding: nonnegative distributions with E[X*] = 1 → probability laws F with F((−∞,0)) = 0, Integrable id F and prophetMean F n = 1; reason: integrability follows from E[X*] = 1 for nonnegative values
--   - encoding: n ≥ n₀ → n with NeZero n and n₀ ≤ n; reason: n₀ is existential, so this only excludes n = 0
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Theorem C.2, p.42 (PDF p.43); (C.1), p.43 (PDF p.44); model §2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MeanOnlyProphet_prophetMean
import Definitions.Def_MeanOnlyProphet_Supplement_HistAlg

open MeasureTheory

namespace MeanOnlyProphet.Supplement

/-- **Theorem C.2 (a strict gap below β* for every randomized, history-dependent algorithm).** Feng,
Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…),
Theorem C.2, p.42 (PDF p.43): "There exist constants ε > 0 and n0 such that for every n ≥ n0 , there are
two nonnegative distributions F0,n and F1,n both with E[X ∗ ] = 1 for which every randomized, history-
dependent algorithm A satisfies min {EF0,n [ALGA ] , EF1,n [ALGA ]} ≤ β ∗ − ε. The pair does not depend
on A." The constant β* is the Hill–Kertz constant of (C.1), p.43 (PDF p.44): "∫_0^1 dy/(D + y − y log y)
= 1, β∗ = 1/(1+D), where D > 0 and 0 · log 0 = 0."

Let `D > 0` solve (C.1) and `β* = 1/(1 + D)`. There are `ε > 0` and `n₀` such that for every `n ≥ n₀`
there are two laws `F₀, F₁` of nonnegative values with finite mean and `E[max of n i.i.d. draws] = 1`
such that every randomized history-dependent algorithm `A` (any seed space, any seed law) satisfies
`min(E_{F₀}[ALG_A], E_{F₁}[ALG_A]) ≤ β* − ε`.

**Formalization Note.** (C.1) enters as a hypothesis on `D`; its solution exists and is unique, so the
hypothesis pins β*. Lean's `Real.log 0 = 0` gives the paper's `0 · log 0 = 0`. The pair is chosen
before `A`, so `A` may even be tailored to it ("even when the algorithm is given two candidate
distributions"). `n ≥ 1` is `NeZero n`. -/
theorem theorem_C_2 :
    ∀ D : ℝ, 0 < D → (∫ y in (0 : ℝ)..1, 1 / (D + y - y * Real.log y)) = 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
        ∃ F₀ F₁ : Measure ℝ, IsProbabilityMeasure F₀ ∧ IsProbabilityMeasure F₁ ∧
          F₀ (Set.Iio 0) = 0 ∧ F₁ (Set.Iio 0) = 0 ∧ Integrable id F₀ ∧ Integrable id F₁ ∧
          prophetMean F₀ n = 1 ∧ prophetMean F₁ n = 1 ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (A : HistAlg n Ω),
            min (A.expectedReward P F₀) (A.expectedReward P F₁) ≤ 1 / (1 + D) - ε := by sorry

end MeanOnlyProphet.Supplement
