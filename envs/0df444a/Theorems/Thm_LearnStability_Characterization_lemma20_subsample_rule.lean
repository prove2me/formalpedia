-- Prove2me | Theorems.Thm_LearnStability_Characterization_lemma20_subsample_rule
-- name    : LearnStability.Characterization.lemma20_subsample_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:11:42.595977+00:00
-- url     : https://prove2.me/theorems/89381a81-0785-4e78-ae60-12bd8c72db5d
-- title:
--   Lemma 20 — every rule has a stable, generalizing sub-sample version that keeps its consistency
-- statement:
--   Let $f$ be a learning problem satisfying the standing assumptions with bound $B$, with $\mathcal H$ nonempty, and let $A$ be a measurable learning rule. Then there is a measurable learning rule $A'$ such that
--
--   1. $A'$ universally generalizes with rate $\dfrac{3B}{\sqrt m}$;
--   2. for every distribution $\mathcal D$ and every sequence $\varepsilon_{\rm cons}$, if $A$ is $\varepsilon_{\rm cons}$-consistent under $\mathcal D$ then $A'$ is consistent under $\mathcal D$ with rate $m\mapsto\varepsilon_{\rm cons}(\lfloor\sqrt m\rfloor)$;
--   3. $A'$ is uniform-RO stable with rate $\dfrac{2B}{\sqrt m}$.
--
--   Lemma 20 turns any universally consistent rule into one that is also universally generalizing and uniformly stable; it is the step that makes the necessity direction of Theorem 7 work.
--
--   **Formalization Note.** $\lfloor\sqrt m\rfloor$ is `Nat.sqrt m`. The rule $A'$ is required to be measurable, since otherwise the generalization clause would hold for trivial reasons. The second clause holds for every sequence $\varepsilon_{\rm cons}$, not only for rates.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2654, Lemma 20

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

open MeasureTheory

namespace LearnStability.Characterization

/-- Lemma 20 (p. 2654): for every (measurable) rule `A` there is a (measurable) rule `A'` such
that
* `A'` universally generalizes with rate `3B/√m`;
* for every `D` and every `ε`, if `A` is `ε`-consistent under `D` then `A'` is consistent
  under `D` with rate `m ↦ ε(⌊√m⌋)` (`Nat.sqrt m = ⌊√m⌋`);
* `A'` is uniform-RO stable with rate `2B/√m`. -/
theorem lemma20_subsample_rule {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) :
    ∃ A' : Rule H Z, MeasurableRule f A' ∧
      UniversallyGeneralizes f A' (fun m => 3 * B / Real.sqrt m) ∧
      (∀ D : Measure Z, IsProbabilityMeasure D → ∀ ε : ℕ → ℝ,
        Consistent f A D ε → Consistent f A' D (fun m => ε (Nat.sqrt m))) ∧
      UniformROStable f A' (fun m => 2 * B / Real.sqrt m) := by sorry

end LearnStability.Characterization
