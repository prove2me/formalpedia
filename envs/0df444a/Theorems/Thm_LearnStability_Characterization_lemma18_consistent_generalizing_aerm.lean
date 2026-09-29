-- Prove2me | Theorems.Thm_LearnStability_Characterization_lemma18_consistent_generalizing_aerm
-- name    : LearnStability.Characterization.lemma18_consistent_generalizing_aerm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:12:42.611412+00:00
-- url     : https://prove2.me/theorems/19132377-8ed1-4446-a61b-de4186f5fda3
-- title:
--   Lemma 18 — under Eq. (12), a consistent and generalizing rule is an AERM
-- statement:
--   Let $f$ be a learning problem satisfying the standing assumptions, with $\mathcal H$ nonempty, $A$ a measurable learning rule and $\mathcal D$ a distribution on $\mathcal Z$. Suppose Equation (12) holds under $\mathcal D$ with rate $\varepsilon_{\rm emp}(m)$, i.e.
--   $$\mathbb E_{S\sim\mathcal D^m}\bigl[|F_S(\hat h_S)-F^*|\bigr]\le\varepsilon_{\rm emp}(m)\qquad(m\ge1),$$
--   and that $A$ is $\varepsilon_{\rm cons}$-consistent and $\varepsilon_{\rm gen}$-generalizing under $\mathcal D$. Then $A$ is an AERM under $\mathcal D$ with rate
--   $$\varepsilon_{\rm emp}(m)+\varepsilon_{\rm gen}(m)+\varepsilon_{\rm cons}(m).$$
--
--   Combined with Lemmas 16 and 20 this shows that a learnable problem has a universal AERM, the necessity direction of Theorem 7.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2653, Lemma 18

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties

open MeasureTheory

namespace LearnStability.Characterization

/-- Lemma 18 (p. 2653): if Equation (12) holds under `D` with rate `ε_emp`, i.e.
`E_{S∼D^m}[|F_S(ĥ_S) − F*|] ≤ ε_emp(m)` for all `m ≥ 1`, and a (measurable) rule `A` is
`ε_cons`-consistent and `ε_gen`-generalizing under `D`, then `A` is an AERM under `D` with
rate `ε_emp + ε_gen + ε_cons`. -/
theorem lemma18_consistent_generalizing_aerm {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εemp εcons εgen : ℕ → ℝ)
    (h12 : ∀ m : ℕ, 1 ≤ m →
      ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) ≤ εemp m)
    (hcons : Consistent f A D εcons) (hgen : Generalizes f A D εgen) :
    IsAERM f A D (fun m => εemp m + εgen m + εcons m) := by sorry

end LearnStability.Characterization
