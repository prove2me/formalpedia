-- Prove2me | Theorems.Thm_FoundationsRL_DECLowerExamples_full_info_dec_lower
-- name    : FoundationsRL.DECLowerExamples.full_info_dec_lower
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:09.438717+00:00
-- url     : https://prove2.me/theorems/3908cd10-1b1c-482f-b557-60bd72cb8a05
-- title:
--   Example 6.6 (cont'd) — bandits with full information have $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M)\gtrsim\varepsilon$ (corrected: $A\ge2$, $\varepsilon\le1$)
-- statement:
--   Let $\mathcal M$ be the full-information bandit class with $A$ actions and rewards in $[0,1]$. There is an absolute constant $c>0$ such that for every $A\ge2$ and every $\varepsilon\in(0,1]$,
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M)\ \ge\ c\,\varepsilon .
--   $$
--
--   Since every decision reveals all rewards, the information constraint does not depend on the decision distribution, and the coefficient is independent of $A$. With Proposition 28 this gives a regret lower bound of order $\sqrt T$.
--
--   **Formalization Note** The constant $c$ is quantified before $A$ and $\varepsilon$, so it is absolute. $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M)$ is the class coefficient $\sup_{\widehat M\in\mathrm{co}(\mathcal M)}\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M\cup\{\widehat M\},\widehat M)$, with values in $[0,\infty]$.
--
--   Differences from the source:
--   - correction: any number A of actions → 2 ≤ A; reason: for A = 1 there is a single decision, every gap is 0 and the coefficient is 0 < c·ε
--   - correction: any ε > 0 → ε ≤ 1; reason: rewards lie in [0, 1], so every gap is at most 1 and the coefficient is at most 1; for any c > 0, c·ε ≤ 1 fails for ε > 1/c, so the bound up to a constant can only hold on a bounded range of ε
--   - reading: the full-information variant of the bandit setting in Example 6.6 → the class of all models M_ν(π) = law of (r(π), r), r ∼ ν, ν a law on [0, 1]^A; reason: Example 6.6 fixes Π = [A], R = [0, 1], the reward r(π) and the observation o = (r(π'))_{π'} but names no smaller class
--   - encoding: dec^c_ε(M) ≳ ε → ∃ c > 0, ∀ A ≥ 2, ∀ ε ∈ (0, 1], ofReal(c·ε) ≤ dec^c_ε(M); reason: the notes' ≳ is up to an absolute constant, quantified before A and ε
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 6.6 (cont'd), p. 111

import Mathlib
import Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDEC
import Definitions.Def_FoundationsRL_DECLowerExamples_fullInfoClass

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FoundationsRL.DECLowerExamples

/-- **Example 6.6 (cont'd): bandits with full information have `dec^c_ε(M) ≳ ε`.** There is an
absolute constant `c > 0` such that for every number of actions `A ≥ 2` and every `ε ∈ (0, 1]`,
`dec^c_ε(M) ≥ c · ε` for the full-information class `M`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 6.6 (cont'd), p. 111 (corrected: `A ≥ 2`, `ε ≤ 1`).

**Formalization Note.** `≳` is an absolute constant, quantified before `A` and `ε`. Rewards lie in
`[0, 1]`, so `dec^c_ε(M) ≤ 1` and the bound can hold only for bounded `ε`; for `A = 1` every gap is
`0`. `dec^c_ε(M)` is the class coefficient `sup_{M̂ ∈ co(M)} dec^c_ε(M ∪ {M̂}, M̂)`. -/
theorem full_info_dec_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ A : ℕ, 2 ≤ A → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ENNReal.ofReal (c * ε) ≤ constrainedDEC ε (fullInfoClass A) := by sorry

end FoundationsRL.DECLowerExamples
