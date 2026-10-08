-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_value_zero_eq_primal
-- name    : InfoRelax.IdealPenalty.value_zero_eq_primal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:14.936021+00:00
-- url     : https://prove2.me/theorems/5050bb3a-5498-475b-9ff8-982d032e5a1e
-- title:
--   §2.1 — the initial value $V_0$ of the recursion (2) equals the primal value (1)
-- statement:
--   Consider a dynamic program in recursive form: a natural filtration $\mathbb F$ with $\mathcal F_0=\{\emptyset,\Omega\}$, a countable action set $X$, nonempty feasible-action sets $A_t(a_0,\dots,a_{t-1})$, and bounded period rewards $r_t(a_0,\dots,a_t)$ that are $\mathcal F_t$-measurable. Let $V_t$ be the value functions of the Bellman recursion (2), with $V_{T+1}=0$. Then, almost surely,
--   $$V_0=\sup_{\alpha\in\mathcal A_{\mathbb F}}\mathbb E[r(\alpha)],$$
--   the optimal value of the primal DP (1) over all nonanticipative policies.
--
--   This identity is what makes the recursion (2) a solution method for (1); it holds whether or not the suprema in (2) are attained.
--
--   **Formalization Note** $V_0(a)$ does not depend on $a$; the statement quantifies over all action sequences. The comparison is made in the extended reals, where the primal value is defined. The countable action set is a pinned regularity assumption that makes the supremum in (2) measurable.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 3, §2.1, the paragraph after eq. (2): "The final value V_0 is equal to the optimal value of (1)."

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **§2.1, the claim after eq. (2)**, Brown, Smith & Sun (2010), Oper. Res., DOI
10.1287/opre.1090.0796, p. 3: "The final value `V_0` is equal to the optimal value of (1)."

In the recursive setting (`RecursiveDP.Valid`: `𝓕_0 = {∅, Ω}`, nonempty feasible sets depending on
past actions, `𝓕_t`-measurable bounded period rewards depending on `a_0, …, a_t`), the value
function `V_0` of the recursion (2) equals, almost surely and for every `a`, the primal value
`sup_{α ∈ 𝒜_𝔽} 𝔼[r(α)]` of (1).

**Formalization Note.** `V_0(a)` does not depend on `a` (it is a function of no actions); the
statement quantifies over all `a`. The claim holds whether or not the suprema in (2) are
attained. Pinned: countable action type with the discrete σ-algebra. The comparison is in
`EReal`, where the primal value lives. -/
theorem value_zero_eq_primal {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid) :
    ∀ a : Fin (T + 1) → X, ∀ᵐ ω ∂μ,
      ((valueFn M μ 0 a ω : ℝ) : EReal) = primalValue μ M.A M.𝔽 M.r := by sorry

end InfoRelax.IdealPenalty
