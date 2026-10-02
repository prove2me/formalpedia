-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_looStable_of_generalizes
-- name    : LearnStability.ERMLOO.looStable_of_generalizes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:54:42.083551+00:00
-- url     : https://prove2.me/theorems/877e6e8c-51f1-46ef-8754-9f0687c4826e
-- title:
--   Proof of Theorem 31, first display — a generalizing ERM is LOO stable with rate ε_gen(m − 1)
-- statement:
--   Let $(\mathcal H,\mathcal Z,f)$ be a learning problem with $\mathcal H$ nonempty and $|f(h;z)|\le B$, let $\mathcal D$ be a probability measure on $\mathcal Z$, and let $A$ be an ERM learning rule. If $A$ generalizes with rate $\varepsilon_{\mathrm{gen}}(m)$ under $\mathcal D$, then it is LOO stable under $\mathcal D$ with rate $\varepsilon_{\mathrm{gen}}(m-1)$: for every $m\ge2$,
--   $$\frac1m\sum_{i=1}^m\mathbb E_{S\sim\mathcal D^m}\Big[\big|f(A(S^{\setminus i});z_i)-f(A(S);z_i)\big|\Big]\le\varepsilon_{\mathrm{gen}}(m-1).$$
--
--   This is the implication from generalization to LOO stability in Theorem 31; it is specific to exact ERMs.
--
--   **Formalization Note.** The rule $A$ is measurable; $f(h;\cdot)$ is measurable for each $h$. The rate is written `fun m => εgen (m - 1)`; LOO stability only evaluates it at $m=n+1$ with $n\ge1$, where it equals $\varepsilon_{\mathrm{gen}}(n)$, so natural-number subtraction never truncates.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2668, proof of Theorem 31, first display

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

open MeasureTheory

namespace LearnStability.ERMLOO
theorem looStable_of_generalizes {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (hERM : IsERMRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εgen : ℕ → ℝ)
    (hgen : Generalizes f A D εgen) :
    LOOStable f A D (fun m => εgen (m - 1)) := by sorry

end LearnStability.ERMLOO
