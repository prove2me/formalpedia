-- Prove2me | Theorems.Thm_LearnStability_Characterization_lemma15_aerm_onAverage_consistent
-- name    : LearnStability.Characterization.lemma15_aerm_onAverage_consistent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:10:29.134157+00:00
-- url     : https://prove2.me/theorems/74dc297b-1117-42cf-9c2c-4273446c5040
-- title:
--   Lemma 15 — an on-average generalizing AERM is consistent
-- statement:
--   Let $f$ be a learning problem satisfying the standing assumptions, with $\mathcal H$ nonempty, $A$ a measurable learning rule and $\mathcal D$ a distribution on $\mathcal Z$. If $A$ is an AERM with rate $\varepsilon_{\rm erm}(m)$ under $\mathcal D$ and on-average generalizes with rate $\varepsilon_{\rm oag}(m)$ under $\mathcal D$, then $A$ is consistent under $\mathcal D$ with rate
--   $$\varepsilon_{\rm cons}(m)=\varepsilon_{\rm oag}(m)+\varepsilon_{\rm erm}(m),$$
--   that is, $\mathbb E_{S\sim\mathcal D^m}[F(A(S))-F^*]\le\varepsilon_{\rm oag}(m)+\varepsilon_{\rm erm}(m)$ for every $m\ge1$.
--
--   With Lemma 11 and Claim 6 this gives the consistency part of Theorem 8 and the sufficiency direction of Theorem 7.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2651, Lemma 15

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties

open MeasureTheory

namespace LearnStability.Characterization

/-- Lemma 15 (p. 2651): if a (measurable) rule is an AERM with rate `ε_erm` and on-average
generalizes with rate `ε_oag` under `D`, then it is consistent with rate `ε_oag + ε_erm`
under `D`. -/
theorem lemma15_aerm_onAverage_consistent {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εerm εoag : ℕ → ℝ)
    (haerm : IsAERM f A D εerm) (hoag : OnAverageGeneralizes f A D εoag) :
    Consistent f A D (fun m => εoag m + εerm m) := by sorry

end LearnStability.Characterization
