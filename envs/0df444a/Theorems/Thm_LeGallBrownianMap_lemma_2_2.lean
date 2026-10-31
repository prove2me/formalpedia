-- Prove2me | Theorems.Thm_LeGallBrownianMap_lemma_2_2
-- name    : LeGallBrownianMap.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:29.062627+00:00
-- url     : https://prove2.me/theorems/f11f1d62-a5ae-4319-a6db-d38c16138a3f
-- title:
--   Lemma 2.2 — labels just before $S_r$ stay below $-r+\sqrt\varepsilon$
-- statement:
--   Let $e$ be a normalized Brownian excursion, $Z$ Brownian labels given $e$, and $S_r=\inf\{s\in[0,1]:Z_s=-r\}$ ($\inf\varnothing=\infty$). There is a constant $\beta_0\in(0,1)$ such that the following holds. For all reals $0<\mu<A$ and $\kappa\in(0,1)$ there is a constant $C_{A,\mu,\kappa}$ such that, for every $r\in[\mu,A]$ and $\varepsilon\in(0,\mu/2)$,
--
--   $$
--   \mathbb P\Big[\{S_r\le1-\kappa\}\cap\Big\{\sup_{s\in[S_r-\varepsilon,S_r]}Z_s\ge -r+\sqrt\varepsilon\Big\}\Big]\le C_{A,\mu,\kappa}\,\varepsilon^{\beta_0}.
--   $$
--
--   The lemma controls the oscillation of the labels just before the first hitting time of a level, an input of the main estimate (Lemma 5.3).
--
--   Differences from the source:
--   - encoding: a normalized Brownian excursion e and labels Z with the conditional law of §2.4 → e = OAI.FKCRT.standardExcursion B (norm of a 3-dimensional Brownian bridge) for three independent Brownian motions B, and Z with IsBrownianLabels (conditional characteristic functions), on any probability space; reason: the Bessel bridge has the law of the normalized excursion and the characteristic-function identity is the conditional Gaussian law; quantifying over all realizations pins the law
--   - encoding: sup over [S_r − ε, S_r] → sup over [0,1] ∩ [S_r − ε, S_r]; reason: Z is only defined on [0,1]
--   - encoding: S_r with inf ∅ = ∞; the probability of the event → hitTime in WithTop ℝ (⊤ = ∞); the outer measure of the event, as a real number; reason: keeps the convention; the outer measure equals the probability for a measurable event
--   - encoding: β₀ and C_{A,µ,κ} constants → chosen before the probability space and the realization of (e, Z); reason: the probability depends only on the law of (e, Z), the same for all realizations
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Lemma 2.2, p.14 (proof in the Appendix)

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_IsBrownianLabels
import Definitions.Def_LeGallBrownianMap_hitTime

open MeasureTheory ProbabilityTheory OAI.FKCRT
open scoped NNReal

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, Lemma 2.2,
p.14 (proved in the Appendix): "There exists a constant β_0 ∈ (0, 1) such that the following
holds. Let µ, A, κ be three reals with 0 < µ < A and κ ∈ (0, 1). There exists a constant
C_{A,µ,κ} such that, for every r ∈ [µ, A] and ε ∈ (0, µ/2),
P[ {S_r ≤ 1 − κ} ∩ { sup_{s∈[S_r−ε, S_r]} Z_s ≥ −r + √ε } ] ≤ C_{A,µ,κ} ε^{β_0}."
Here `S_r = inf{s ∈ [0,1] : Z_s = −r}` (`inf ∅ = ∞`).

There is `β₀ ∈ (0,1)` such that for all `0 < µ < A` and `κ ∈ (0,1)` there is `C` such that, for
every realization of `(e, Z)` and all `r ∈ [µ, A]`, `ε ∈ (0, µ/2)`, the probability that
`S_r ≤ 1 − κ` and `sup_{s ∈ [S_r − ε, S_r]} Z_s ≥ −r + √ε` is at most `C ε^{β₀}`.

**Formalization Note.** `(e, Z)` is realized as in `LeGallBrownianMap.theorem_1_1`; the
constants are chosen before the realization (the probability depends only on the law of `Z`).
`S_r` is `hitTime` in `WithTop ℝ` (`⊤ = ∞`), so `{S_r ≤ 1 − κ}` requires `S_r` finite. `Z` is
defined on `[0,1]` only, so the supremum runs over `[0,1] ∩ [S_r − ε, S_r]` (the interval is
clipped when `S_r < ε`). The probability is the outer measure `P`, as a real number. -/
theorem lemma_2_2 :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ < 1 ∧
      ∀ μ A κ : ℝ, 0 < μ → μ < A → 0 < κ → κ < 1 → ∃ C : ℝ,
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : Fin 3 → ℝ≥0 → Ω → ℝ), (∀ i, IsBrownianReal (B i) P) →
          iIndepFun (fun i ω t => B i t ω) P →
          ∀ Z : unitInterval → Ω → ℝ, IsBrownianLabels (fun ω => standardExcursion B ω) Z P →
          ∀ r ∈ Set.Icc μ A, ∀ ε ∈ Set.Ioo 0 (μ / 2),
            (P {ω | ∃ S : ℝ, hitTime (fun s => Z s ω) r = (S : WithTop ℝ) ∧ S ≤ 1 - κ ∧
                -r + Real.sqrt ε ≤
                  sSup ((fun s => Z s ω) '' {s : unitInterval | S - ε ≤ s ∧ (s : ℝ) ≤ S})}).toReal
              ≤ C * ε ^ β₀ := by sorry

end LeGallBrownianMap
