-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_lemma16_main_converse
-- name    : LearnStability.ERMLOO.lemma16_main_converse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:41:42.579524+00:00
-- url     : https://prove2.me/theorems/f4fdbe56-1487-4e97-b7f5-4b8883843068
-- title:
--   Lemma 16 (Main Converse Lemma) — in a learnable problem the ERM value estimates F* at rate 2ε_cons(m′) + 2B/√m + 2Bm′²/m
-- statement:
--   Let $(\mathcal H,\mathcal Z,f)$ be a learning problem with $\mathcal H$ nonempty and $|f(h;z)|\le B$, and suppose it is learnable: some learning rule $A$ is consistent with rate $\varepsilon_{\mathrm{cons}}(m)$ under every probability measure on $\mathcal Z$. Then for every probability measure $\mathcal D$ on $\mathcal Z$ and all integers $m,m'$ with $2\le m'\le m/2$,
--   $$\mathbb E_{S\sim\mathcal D^m}\Big[\big|F_S(\hat h_S)-F^*\big|\Big]\le\varepsilon_{\mathrm{emp}}(m):=2\varepsilon_{\mathrm{cons}}(m')+\frac{2B}{\sqrt m}+\frac{2Bm'^2}{m},$$
--   where $F_S(\hat h_S)=\inf_{h\in\mathcal H}F_S(h)$ is the minimal empirical risk. This is Eq. (12).
--
--   The lemma says that, although an ERM may fail to learn, its empirical risk is a consistent estimator of the optimal risk as soon as the problem is learnable at all; this is where universality of the consistency rate is used, and it drives the implication from consistency to generalization.
--
--   **Formalization Note.** The rule $A$ is measurable and the ERM value $S\mapsto\inf_hF_S(h)$ is measurable; $f(h;\cdot)$ is measurable for each $h$. The rate $\varepsilon_{\mathrm{cons}}$ need not be monotone for this lemma. The condition $m'\le m/2$ is written $2m'\le m$.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2652, Lemma 16 (Main Converse Lemma), Eq. (12)

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

open MeasureTheory

namespace LearnStability.ERMLOO
theorem lemma16_main_converse {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A) (εcons : ℕ → ℝ)
    (hcons : UniversallyConsistent f A εcons)
    (D : Measure Z) [IsProbabilityMeasure D] (m m' : ℕ) (hm'₁ : 2 ≤ m') (hm'₂ : 2 * m' ≤ m) :
    ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m)
      ≤ 2 * εcons m' + 2 * B / Real.sqrt m + 2 * B * (m' : ℝ) ^ 2 / m := by sorry

end LearnStability.ERMLOO
