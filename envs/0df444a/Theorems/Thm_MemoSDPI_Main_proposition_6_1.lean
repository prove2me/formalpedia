-- Prove2me | Theorems.Thm_MemoSDPI_Main_proposition_6_1
-- name    : MemoSDPI.Main.proposition_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:43:05.861627+00:00
-- url     : https://prove2.me/theorems/2696ceae-07f8-4279-ba35-01d6c5bfaf37
-- title:
--   Proposition 6.1 — an (ε, δ)-DP algorithm on n i.i.d. records from a countable D reveals ≤ n[min{ε, ε tanh(ε/2)+(1+ε)δ} + δH(D) + δ] nats
-- statement:
--   Let $\varepsilon > 0$, $\delta \in [0,1]$, and let $A$ be an $(\varepsilon,\delta)$-differentially private algorithm (replacement adjacency: for adjacent datasets $s, s'$ of the same size differing in one record and every set of outputs $E$, $\Pr[A(s)\in E] \le e^\varepsilon \Pr[A(s')\in E] + \delta$). Then for every distribution $D$ on a countable domain with $H(D) < \infty$ and $S \sim D^n$,
--   $$
--   I(A(S); S) \;\le\; n\Big[\min\{\varepsilon,\ \varepsilon\tanh(\varepsilon/2) + (1+\varepsilon)\delta\} + \delta H(D) + \delta\Big].
--   $$
--   In particular, for $0 < \varepsilon \le 1$,
--   $$
--   I(A(S); S) \;\le\; n\Big(\frac{\varepsilon^2}{2} + \delta\big(H(D) + 3\big)\Big). \tag{6.1}
--   $$
--   $H(D)$ is the Shannon entropy in nats. With $D$ a product Bernoulli law on $\{0,1\}^m$ ($H(D) \le m\log 2$), (6.1) is the privacy half of Theorem 7.4.
--
--   **Formalization Note** The domain is a countable type with measurable singletons and $D$ a probability measure on it; the output space is arbitrary. Differential privacy is the published `DPVerify.IsDPAlg` (replacement adjacency, every measurable output set). $I(A(S);S)$ is the mission's `memD A D`. The right-hand sides are computed in $[0,\infty]$ from nonnegative terms, which equals the real expression because $H(D) < \infty$.
--
--   Differences from the source:
--   - encoding: D on a countable domain → D a probability measure on a Countable type with MeasurableSingletonClass; reason: same distributions
--   - encoding: real bound n[… + δH(D) + δ] → the same expression in ℝ≥0∞ with ENNReal.ofReal of the nonnegative real parts and H(D) ∈ ℝ≥0∞; reason: all terms are nonnegative and H(D) < ∞, so the two values agree
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 24, Proposition 6.1 (proof in Appendix A, pp. 35–36)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsDPAlg
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_Memorization
import Definitions.Def_MemoSDPI_Main_ShannonEntropy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 24, Proposition 6.1 (proved in Appendix A, pp. 35–36): for `ε > 0`, `δ ∈ [0, 1]`, an
`(ε, δ)`-differentially private `A`, and a distribution `D` on a countable domain with
`H(D) < ∞` and `S ∼ D^n`: `I(A(S); S) ≤ n [min{ε, ε tanh(ε/2) + (1 + ε)δ} + δH(D) + δ]`, and for
`0 < ε ≤ 1`, `I(A(S); S) ≤ n (ε²/2 + δ(H(D) + 3))` (6.1). -/
theorem proposition_6_1 {X Y : Type} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] [MeasurableSpace Y] {n : ℕ} (A : DPVerify.RandAlg X Y n) (ε δ : ℝ)
    (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hDP : DPVerify.IsDPAlg A ε δ)
    (D : Measure X) [IsProbabilityMeasure D] (hH : shannonEntropy D ≠ ∞) :
    memD A D ≤ (n : ℝ≥0∞) *
        (ENNReal.ofReal (min ε (ε * Real.tanh (ε / 2) + (1 + ε) * δ)) +
          ENNReal.ofReal δ * shannonEntropy D + ENNReal.ofReal δ) ∧
      (ε ≤ 1 → memD A D ≤ (n : ℝ≥0∞) *
        (ENNReal.ofReal (ε ^ 2 / 2) + ENNReal.ofReal δ * (shannonEntropy D + 3))) := by sorry

end MemoSDPI.Main
