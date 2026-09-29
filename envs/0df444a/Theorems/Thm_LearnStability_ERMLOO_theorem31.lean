-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_theorem31
-- name    : LearnStability.ERMLOO.theorem31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:01:13.199983+00:00
-- url     : https://prove2.me/theorems/e1a6c9b8-bc5c-4dc6-b8fb-4011a95b9a4b
-- title:
--   Theorem 31 — for an ERM, universal LOO stability, universal consistency and universal generalization are equivalent
-- statement:
--   Let $(\mathcal H,\mathcal Z,f)$ be a learning problem with $\mathcal H$ nonempty and $|f(h;z)|\le B$ for all $h,z$, and let $A$ be an ERM, i.e. a learning rule with $F_S(A(S))=\inf_{h\in\mathcal H}F_S(h)$ for every sample $S$. Then the following are equivalent:
--
--   1. $A$ is universally LOO stable: there is a rate $\varepsilon$ such that $A$ is LOO stable with rate $\varepsilon$ under every probability measure $\mathcal D$ on $\mathcal Z$;
--   2. $A$ is universally consistent: there is a rate $\varepsilon$ such that $\mathbb E_{S\sim\mathcal D^m}[F(A(S))-F^*]\le\varepsilon(m)$ for all $m\ge1$ and every $\mathcal D$;
--   3. $A$ universally generalizes: there is a rate $\varepsilon$ such that $\mathbb E_{S\sim\mathcal D^m}[|F(A(S))-F_S(A(S))|]\le\varepsilon(m)$ for all $m\ge1$ and every $\mathcal D$.
--
--   Here a rate is a sequence non-increasing in $m\ge1$ and tending to $0$, and in each item one rate serves all distributions.
--
--   In particular LOO stability is necessary for a consistent ERM. The ERM hypothesis cannot be relaxed to an asymptotic ERM: the paper's Example 6 exhibits a universally consistent AERM that is not LOO stable.
--
--   **Formalization Note.** Stated as $(1\Leftrightarrow2)\wedge(2\Leftrightarrow3)$. Standing assumptions made explicit: $\mathcal H$ nonempty, $|f|\le B$, each $f(h;\cdot)$ measurable, and the rule measurable ($(S,z)\mapsto f(A(S);z)$ jointly measurable for every $m$); for a measurable ERM the ERM value is then measurable, so no separate assumption on it is made. The ERM condition is imposed for all sample sizes $m\ge1$; the rule's value at $m=0$ is never used.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2667, Theorem 31

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

open MeasureTheory

namespace LearnStability.ERMLOO
theorem theorem31 {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (hERM : IsERMRule f A) :
    ((∃ ε, IsRate ε ∧ UniversallyLOOStable f A ε) ↔ (∃ ε, IsRate ε ∧ UniversallyConsistent f A ε)) ∧
    ((∃ ε, IsRate ε ∧ UniversallyConsistent f A ε) ↔
      (∃ ε, IsRate ε ∧ UniversallyGeneralizes f A ε)) := by sorry

end LearnStability.ERMLOO
