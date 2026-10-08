-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_eq_10_dual_recursion
-- name    : InfoRelax.IdealPenalty.eq_10_dual_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:26.835993+00:00
-- url     : https://prove2.me/theorems/ca6b87ec-e2cc-40fd-8e42-80ae928504f6
-- title:
--   §2.3, eq. (10) — the dual recursion solves the dual problem and bounds the primal DP
-- statement:
--   Consider a recursive DP (natural filtration with $\mathcal F_0=\{\emptyset,\Omega\}$, countable action set, nonempty feasible sets $A_t(a_0,\dots,a_{t-1})$, bounded $\mathcal F_t$-measurable period rewards $r_t(a_0,\dots,a_t)$). Let $\mathbb G$ be a relaxation of $\mathbb F$, let $(w_t)$ be generating functions as in Proposition 2.2 and $z=\sum_t z_t$ the penalty they generate. Let $V^{\mathbb G}_t$ be the dual value functions of (10): $V^{\mathbb G}_{T+1}=0$ and
--   $$V^{\mathbb G}_t(a_0,\dots,a_{t-1})=\sup_{a_t\in A_t(a_0,\dots,a_{t-1})}\big\{r_t(a_0,\dots,a_t)-z_t(a_0,\dots,a_t)+\mathbb E[V^{\mathbb G}_{t+1}(a_0,\dots,a_t)\mid\mathcal G_t]\big\}.$$
--   Then the recursion solves the dual problem for $(\mathbb G,z)$ and its initial value bounds the primal DP:
--   $$\mathbb E[V^{\mathbb G}_0]=\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z(\alpha_G)],\qquad \sup_{\alpha_F\in\mathcal A_{\mathbb F}}\mathbb E[r(\alpha_F)]\le\mathbb E[V^{\mathbb G}_0].$$
--
--   **Formalization Note** $V^{\mathbb G}_0$ is $\mathcal G_0$-measurable but in general not constant; the page's "initial value" is read as its expectation. $V^{\mathbb G}_0(a)$ does not depend on $a$, and the statement quantifies over all $a$. Values are extended reals.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, §2.3, eq. (10) and the sentence after it

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **§2.3, eq. (10)**, Brown, Smith & Sun (2010), Oper. Res., DOI 10.1287/opre.1090.0796, p. 5.

In the recursive setting, let `𝔾` be a relaxation of `𝔽`, `w` generating functions as in
Proposition 2.2 and `z = ∑_t z_t` the penalty it constructs. The dual value functions `V^𝔾_t` of
(10) (the recursion (2) with rewards `r_t − z_t` and filtration `𝔾`, `V^𝔾_{T+1} = 0`) solve the
dual problem, `𝔼[V^𝔾_0] = sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)]`, and the initial value provides an
upper bound on the primal DP (1): `sup_{α_F ∈ 𝒜_𝔽} 𝔼[r(α_F)] ≤ 𝔼[V^𝔾_0]`.

**Formalization Note.** `V^𝔾_0` is `𝒢_0`-measurable but not constant in general; the page's
"initial value" is read as its expectation. `V^𝔾_0(a)` does not depend on `a`; the statement
quantifies over all `a`. Pinned: countable action type with the discrete σ-algebra, generating
functions as in `GeneratingFns`. -/
theorem eq_10_dual_recursion {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : IsRelaxation M.𝔽 𝔾)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (hw : GeneratingFns μ w) :
    ∀ a : Fin (T + 1) → X,
      ((∫ ω, dualValueFn M μ 𝔾 w 0 a ω ∂μ : ℝ) : EReal) =
          dualBound μ M.A 𝔾 M.r (penalty μ M.𝔽 𝔾 w) ∧
        primalValue μ M.A M.𝔽 M.r ≤ ((∫ ω, dualValueFn M μ 𝔾 w 0 a ω ∂μ : ℝ) : EReal) := by sorry

end InfoRelax.IdealPenalty
