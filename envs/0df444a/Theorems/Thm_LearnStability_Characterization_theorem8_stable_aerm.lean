-- Prove2me | Theorems.Thm_LearnStability_Characterization_theorem8_stable_aerm
-- name    : LearnStability.Characterization.theorem8_stable_aerm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:11:04.540027+00:00
-- url     : https://prove2.me/theorems/57bd7f28-5d66-486d-8584-c98a88e64543
-- title:
--   Theorem 8 — a stable AERM is consistent and generalizes, with rates
-- statement:
--   Let $f$ be a learning problem satisfying the standing assumptions with bound $B$, with $\mathcal H$ nonempty, let $A$ be a measurable learning rule and $\mathcal D$ a distribution on $\mathcal Z$. Suppose $A$ is an AERM with rate $\varepsilon_{\rm erm}(m)$ under $\mathcal D$, and that $A$ is average-RO stable with rate $\varepsilon_{\rm stable}(m)$ under $\mathcal D$ or uniform-RO stable with rate $\varepsilon_{\rm stable}(m)$. Then $A$ is consistent and generalizes under $\mathcal D$ with rates
--   $$\varepsilon_{\rm cons}(m)\le\varepsilon_{\rm stable}(m)+\varepsilon_{\rm erm}(m),\qquad \varepsilon_{\rm gen}(m)\le\varepsilon_{\rm stable}(m)+2\varepsilon_{\rm erm}(m)+\frac{2B}{\sqrt m}.$$
--
--   The sufficiency direction of Theorem 7 (a uniform-RO stable universal AERM is universally consistent) is the consistency clause applied under every distribution.
--
--   **Formalization Note.** The conclusion is stated as "consistent with rate $m\mapsto\varepsilon_{\rm stable}(m)+\varepsilon_{\rm erm}(m)$" and "generalizes with rate $m\mapsto\varepsilon_{\rm stable}(m)+2\varepsilon_{\rm erm}(m)+2B/\sqrt m$" for every $m\ge1$; the hypotheses do not require the rates to be monotone, since the proof does not use it.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2649, Theorem 8

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

open MeasureTheory

namespace LearnStability.Characterization

/-- Theorem 8 (p. 2649): if a (measurable) rule is an AERM with rate `ε_erm` and average-RO
stable (or uniform-RO stable) with rate `ε_stable` under `D`, then under `D` it is
consistent with rate `ε_stable + ε_erm` and generalizes with rate
`ε_stable + 2 ε_erm + 2B/√m`. -/
theorem theorem8_stable_aerm {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εerm εstable : ℕ → ℝ)
    (haerm : IsAERM f A D εerm)
    (hstab : AverageROStable f A D εstable ∨ UniformROStable f A εstable) :
    Consistent f A D (fun m => εstable m + εerm m) ∧
      Generalizes f A D (fun m => εstable m + 2 * εerm m + 2 * B / Real.sqrt m) := by sorry

end LearnStability.Characterization
