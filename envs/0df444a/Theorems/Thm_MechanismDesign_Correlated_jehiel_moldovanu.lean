-- Prove2me | Theorems.Thm_MechanismDesign_Correlated_jehiel_moldovanu
-- name    : MechanismDesign.Correlated.jehiel_moldovanu
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T02:45:28.346814+00:00
-- url     : https://prove2.me/theorems/b921993c-9b91-47b8-8cf6-b050140de291
-- title:
--   Proposition 9.1 (Jehiel–Moldovanu) — with interdependent values, no first best direct mechanism is Bayesian incentive-compatible
-- statement:
--   **Proposition 9.1 (Jehiel and Moldovanu 2001).** Consider the model of §9.3: agents $i\in I$ observe independent signals $\theta^i\in[0,1]^K$ with everywhere-positive densities, and agent $i$'s utility from alternative $a_k$ is $\sum_{j=1}^N \alpha^j_{ki}\theta^j_k - t_i$ with all $\alpha^j_{ki}\ne 0$. Assume that every first best choice rule $q^*$ has interim probabilities $Q^i_a$ that are differentiable on $[0,1]^K$ with derivative never zero:
--   $$\frac{\partial Q^i_a(\theta^i)}{\partial \theta^i_b} \ne 0 \quad\text{for every } i\in I,\ a,b\in A,\ \theta^i\in[0,1]^K.$$
--   Assume also that there are an agent $i\in I$ and two alternatives $a,b\in A$ such that
--   $$\frac{\alpha^i_{ai}}{\alpha^i_{bi}} \ne \frac{\sum_{j=1}^N \alpha^i_{aj}}{\sum_{j=1}^N \alpha^i_{bj}}.$$
--   Then no first best direct mechanism is Bayesian incentive-compatible.
--
--   The second condition says that the relative weight agent $i$ attaches to his signal components for $a$ and $b$ differs from the relative weight social welfare attaches to them; it holds for generic weights. The result needs neither individual rationality nor budget balance, in contrast with the impossibility results for private values.
--
--   **Formalization Note** Differentiability on the closed cube is differentiability within $[0,1]^K$, and $\partial Q^i_a/\partial\theta^i_b$ is the derivative within $[0,1]^K$ in the direction of the $b$-th unit vector. The first hypothesis ranges over measurable first best choice rules (the book omits measurability); the proof on p.160 assumes in addition that interim utilities are twice continuously differentiable, which is a device of that proof, not a hypothesis of the proposition, and is not assumed. Where a denominator $\sum_j\alpha^i_{bj}$ would vanish, the first hypothesis already fails (no first best rule then needs to react to $\theta^i_b$), so Lean's convention $x/0=0$ does not change the statement's content.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.159–160, Proposition 9.1 (model §9.3 p.158)

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_InterdependentModel

namespace MechanismDesign.Correlated

open Interdependent

/-- Börgers, Proposition 9.1 (pp.159–160), after Jehiel and Moldovanu (2001). In the model of
§9.3, assume that for every first best choice rule `q*` the interim probabilities `Qⁱ_a` are
differentiable on `[0,1]^K` with `∂Qⁱ_a(θⁱ)/∂θⁱ_b ≠ 0` for all `i`, `a`, `b` and `θⁱ ∈ [0,1]^K`,
and that for some agent `i` and alternatives `a, b`,
`α^i_{ai} / α^i_{bi} ≠ (∑_j α^i_{aj}) / (∑_j α^i_{bj})`. Then no first best direct mechanism is
Bayesian incentive-compatible. -/
theorem jehiel_moldovanu {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [Fintype A]
    [DecidableEq A] (S : Setting ι A)
    (hdiff : ∀ q, IsChoiceRule q → S.IsFirstBest q → ∀ (i : ι) (a b : A), ∀ x ∈ cube A,
      DifferentiableWithinAt ℝ (S.interimProb q i a) (cube A) x ∧
        fderivWithin ℝ (S.interimProb q i a) (cube A) x (Pi.single b 1) ≠ 0)
    (hα : ∃ (i : ι) (a b : A),
      S.α i a i / S.α i b i ≠ (∑ j, S.α i a j) / (∑ j, S.α i b j)) :
    ∀ M : Mechanism ι A, S.IsDirect M → S.IsFirstBest M.q → ¬ S.IsBIC M := by sorry

end MechanismDesign.Correlated
