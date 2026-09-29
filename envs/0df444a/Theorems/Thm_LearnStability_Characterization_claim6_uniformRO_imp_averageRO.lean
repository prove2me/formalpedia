-- Prove2me | Theorems.Thm_LearnStability_Characterization_claim6_uniformRO_imp_averageRO
-- name    : LearnStability.Characterization.claim6_uniformRO_imp_averageRO
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:09:42.263675+00:00
-- url     : https://prove2.me/theorems/0e81f4c4-c2fe-4ec9-8912-a907933e5252
-- title:
--   Claim 6 — uniform-RO stability implies average-RO stability with the same rate
-- statement:
--   Let $f$ be a learning problem satisfying the standing assumptions and $A$ a measurable learning rule. If $A$ is uniform-RO stable with rate $\varepsilon_{\rm stable}(m)$, then for every probability distribution $\mathcal D$ on $\mathcal Z$ it is average-RO stable with rate $\varepsilon_{\rm stable}(m)$ under $\mathcal D$:
--   $$\Bigl|\frac1m\sum_{i=1}^m\mathbb E\bigl[f(A(S^{(i)});z_i')-f(A(S);z_i')\bigr]\Bigr|\le\varepsilon_{\rm stable}(m)\qquad(m\ge1).$$
--
--   The implication is not a direct specialisation: Definition 4 uses one test point $z'$ for all $i$, whereas Definition 5 tests at the replacement point $z_i'$. Claim 6 lets the sufficiency direction of Theorem 7 use the in-expectation machinery of Lemmas 11 and 15.
--
--   **Formalization Note.** The paper states Claim 6 without proof and without quantifying the distribution; it is read as holding under every distribution (the paper calls this "universally" stable, p. 2648).
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2648, Claim 6

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

open MeasureTheory

namespace LearnStability.Characterization

/-- Claim 6 (p. 2648): a (measurable) rule that is uniform-RO stable with rate `ε` is
average-RO stable with rate `ε` under every distribution `D`. -/
theorem claim6_uniformRO_imp_averageRO {H Z : Type*} [MeasurableSpace Z]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (ε : ℕ → ℝ)
    (hstab : UniformROStable f A ε) :
    ∀ D : Measure Z, IsProbabilityMeasure D → AverageROStable f A D ε := by sorry

end LearnStability.Characterization
