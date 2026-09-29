-- Prove2me | Theorems.Thm_LearnStability_Characterization_lemma11_onAverage_iff_averageRO
-- name    : LearnStability.Characterization.lemma11_onAverage_iff_averageRO
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:09:08.886924+00:00
-- url     : https://prove2.me/theorems/69c34d17-0490-40a2-9c23-462e08b2aad8
-- title:
--   Lemma 11 — on-average generalization is equivalent to average-RO stability
-- statement:
--   Let $f$ be a learning problem satisfying the standing assumptions with bound $B$, let $A$ be a measurable learning rule, $\mathcal D$ a distribution on $\mathcal Z$ and $\varepsilon(m)$ a sequence. Then:
--
--   1. if $A$ on-average generalizes with rate $\varepsilon$ under $\mathcal D$, it is average-RO stable with rate $\varepsilon$ under $\mathcal D$;
--   2. if $A$ is average-RO stable with rate $\varepsilon$ under $\mathcal D$, it on-average generalizes with rate $\varepsilon$ under $\mathcal D$.
--
--   The equivalence rests on the identity
--   $$\mathbb E_{S}[F(A(S))-F_S(A(S))]=\frac1m\sum_{i=1}^m\mathbb E_{S,(z_1',\dots,z_m')}\bigl[f(A(S);z_i')-f(A(S^{(i)});z_i')\bigr].$$
--   It is the bridge from stability to consistency (with Lemma 15) and back.
--
--   **Formalization Note.** Measurability of the rule is the convention of the `Setting` file; the standing assumptions include $|f|\le B$, which makes all expectations finite.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2650, Lemma 11

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

open MeasureTheory

namespace LearnStability.Characterization

/-- Lemma 11 (p. 2650): under a fixed distribution `D`, a (measurable) rule is on-average
generalizing with rate `ε` if and only if it is average-RO stable with rate `ε`. -/
theorem lemma11_onAverage_iff_averageRO {H Z : Type*} [MeasurableSpace Z]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (ε : ℕ → ℝ) :
    (OnAverageGeneralizes f A D ε → AverageROStable f A D ε) ∧
      (AverageROStable f A D ε → OnAverageGeneralizes f A D ε) := by sorry

end LearnStability.Characterization
