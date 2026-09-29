-- Prove2me | Theorems.Thm_LearnStability_Characterization_theorem7_learnable_iff_stable_aerm
-- name    : LearnStability.Characterization.theorem7_learnable_iff_stable_aerm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:13:18.874095+00:00
-- url     : https://prove2.me/theorems/be2ab818-0bda-4fad-89a0-a7239dc68a7e
-- title:
--   Theorem 7 — a problem is learnable iff it has a uniform-RO stable, universally AERM learning rule
-- statement:
--   Let $f:\mathcal H\times\mathcal Z\to\mathbb R$ be a learning problem with $\mathcal H$ nonempty, satisfying the standing assumptions with bound $B$ ($|f|\le B$, measurable losses, measurable minimal empirical risk). Then:
--
--   1. The problem is learnable if and only if there exists a measurable learning rule that is uniform-RO stable with some rate and universally an AERM with some rate.
--   2. If a measurable rule is universally consistent with rate $\varepsilon_{\rm cons}(m)$ (non-increasing, tending to $0$), then there exists a measurable rule that is $\varepsilon_{\rm stable}(m)$-uniform-RO stable and universally $\varepsilon_{\rm erm}(m)$-AERM, where
--   $$\varepsilon_{\rm erm}(m)=3\varepsilon_{\rm cons}\bigl(\lfloor m^{1/4}\rfloor\bigr)+\frac{8B}{\sqrt m},\qquad \varepsilon_{\rm stable}(m)=\frac{2B}{\sqrt m}.$$
--   3. Conversely, if a measurable rule is $\varepsilon_{\rm stable}(m)$-uniform-RO stable and universally $\varepsilon_{\rm erm}(m)$-AERM, then it is universally consistent with rate
--   $$\varepsilon_{\rm cons}(m)\le\varepsilon_{\rm stable}(m)+\varepsilon_{\rm erm}(m).$$
--
--   In the General Learning Setting learnability is not equivalent to uniform convergence, and a learnable problem need not be learnable by empirical risk minimisation; the theorem shows that stability of an asymptotic empirical risk minimiser characterises learnability exactly, with explicit rates in both directions.
--
--   **Formalization Note.** $\lfloor m^{1/4}\rfloor$ is `Nat.sqrt (Nat.sqrt m)`; the paper writes $\varepsilon_{\rm cons}(m^{1/4})$. All rules, both in the hypotheses and in the conclusions, are measurable in the sense of the `Setting` file, and rates are non-increasing on $m\ge1$ and tend to $0$. The measurability of $S\mapsto\inf_hF_S(h)$ is a standing assumption of this formalization (it holds e.g. for countable $\mathcal H$). In clause 3 the rates need not be monotone.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), pp. 2648–2649, Theorem 7

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

open MeasureTheory

namespace LearnStability.Characterization

/-- Theorem 7 (pp. 2648–2649). For a learning problem satisfying the standing assumptions:
1. it is learnable iff there is a (measurable) rule that is uniform-RO stable and universally
   an AERM (each with some rate);
2. if `A` is universally consistent with rate `ε_cons`, some (measurable) rule `A'` is
   uniform-RO stable with rate `2B/√m` and universally an AERM with rate
   `3 ε_cons(⌊m^{1/4}⌋) + 8B/√m` (`Nat.sqrt (Nat.sqrt m) = ⌊m^{1/4}⌋`);
3. a (measurable) rule that is uniform-RO stable with rate `ε_stable` and universally an AERM
   with rate `ε_erm` is universally consistent with rate `ε_stable + ε_erm`. -/
theorem theorem7_learnable_iff_stable_aerm {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B) :
    (Learnable f ↔
      ∃ A : Rule H Z, MeasurableRule f A ∧ ∃ εstable εerm : ℕ → ℝ,
        IsRate εstable ∧ IsRate εerm ∧
        UniformROStable f A εstable ∧ UniversalAERM f A εerm) ∧
    (∀ (A : Rule H Z) (εcons : ℕ → ℝ), MeasurableRule f A → IsRate εcons →
      UniversallyConsistent f A εcons →
      ∃ A' : Rule H Z, MeasurableRule f A' ∧
        UniformROStable f A' (fun m => 2 * B / Real.sqrt m) ∧
        UniversalAERM f A'
          (fun m => 3 * εcons (Nat.sqrt (Nat.sqrt m)) + 8 * B / Real.sqrt m)) ∧
    (∀ (A : Rule H Z) (εstable εerm : ℕ → ℝ), MeasurableRule f A →
      UniformROStable f A εstable → UniversalAERM f A εerm →
      UniversallyConsistent f A (fun m => εstable m + εerm m)) := by sorry

end LearnStability.Characterization
