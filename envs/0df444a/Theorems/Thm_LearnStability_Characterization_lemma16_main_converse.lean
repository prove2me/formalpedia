-- Prove2me | Theorems.Thm_LearnStability_Characterization_lemma16_main_converse
-- name    : LearnStability.Characterization.lemma16_main_converse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:12:13.28162+00:00
-- url     : https://prove2.me/theorems/36f6a5d4-37fb-4bbb-b3f8-ab1194813274
-- title:
--   Lemma 16 (Main Converse Lemma) — in a learnable problem the minimal empirical risk estimates F*
-- statement:
--   Let $f$ be a learning problem satisfying the standing assumptions with bound $B$, with $\mathcal H$ nonempty, and let $A$ be a measurable learning rule that is universally consistent with rate $\varepsilon_{\rm cons}(m)$. Then for every distribution $\mathcal D$ on $\mathcal Z$ and all natural numbers $m,m'$ with $2\le m'\le m/2$,
--   $$\mathbb E_{S\sim\mathcal D^m}\bigl[|F_S(\hat h_S)-F^*|\bigr]\le\varepsilon_{\rm emp}(m):=2\varepsilon_{\rm cons}(m')+\frac{2B}{\sqrt m}+\frac{2Bm'^2}{m}.\tag{12}$$
--
--   Although the empirical risk minimiser itself may fail to learn, its value $\inf_h F_S(h)$ is a consistent estimator of the optimal risk $F^*$ whenever the problem is learnable. This is the step in which universal consistency (under every distribution, in particular the empirical one) is essential.
--
--   **Formalization Note.** $F_S(\hat h_S)$ is the infimum $\inf_h F_S(h)$. The paper's condition $2\le m'\le m/2$ is written $2\le m'$ and $2m'\le m$ with $m,m'$ natural numbers. The hypothesis does not require $\varepsilon_{\rm cons}$ to be monotone.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2652, Lemma 16, Eq. (12)

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties

open MeasureTheory

namespace LearnStability.Characterization

/-- Lemma 16, Main Converse Lemma (p. 2652): if a (measurable) rule `A` is universally
consistent with rate `ε_cons`, then under every distribution `D`, for all `m` and every
`m'` with `2 ≤ m' ≤ m/2`,
`E_{S∼D^m}[|F_S(ĥ_S) − F*|] ≤ 2 ε_cons(m') + 2B/√m + 2B m'^2/m`. -/
theorem lemma16_main_converse {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (εcons : ℕ → ℝ)
    (hcons : UniversallyConsistent f A εcons)
    (D : Measure Z) [IsProbabilityMeasure D]
    (m m' : ℕ) (hm'2 : 2 ≤ m') (hm'm : 2 * m' ≤ m) :
    ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) ≤
      2 * εcons m' + 2 * B / Real.sqrt m + 2 * B * (m' : ℝ) ^ 2 / m := by sorry

end LearnStability.Characterization
