-- Prove2me | Theorems.Thm_InfoRelax_RelaxOrder_eq_10_dual_recursion
-- name    : InfoRelax.RelaxOrder.eq_10_dual_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:40.535651+00:00
-- url     : https://prove2.me/theorems/8fc9cb11-4e59-433a-a4ec-6401befda303
-- title:
--   §2.3, eq. (10) — the dual recursion solves the dual problem for a Proposition 2.2 penalty
-- statement:
--   Consider a dynamic program in recursive form with countable action set (natural filtration $\mathbb F$ with $\mathcal F_0=\{\emptyset,\Omega\}$, nonempty feasible-action sets $A_t(a_0,\dots,a_{t-1})$, bounded $\mathcal F_t$-measurable period rewards $r_t(a_0,\dots,a_t)$). Let $\mathbb G$ be a relaxation of $\mathbb F$, let $(w_0,\dots,w_T)$ be regular generating functions, and let
--   $$z_t(a)=\mathbb E[w_t(a)\mid\mathcal G_t]-\mathbb E[w_t(a)\mid\mathcal F_t],\qquad z(a)=\sum_{t=0}^T z_t(a)$$
--   be the penalty of Proposition 2.2. Let $V^{\mathbb G}_t$ be the dual value functions of (10), computed with the penalized rewards $r_t-z_t$ and conditional expectations given $\mathcal G_t$, with $V^{\mathbb G}_{T+1}=0$. Then the recursion solves the dual problem:
--   $$\mathbb E\big[V^{\mathbb G}_0\big]=\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E\big[r(\alpha_G)-z(\alpha_G)\big].$$
--
--   Applied to two relaxations $\mathbb G^1\subseteq\mathbb G^2$, it turns the comparison of the dual bounds in Proposition 2.3(i) into a comparison of two backward recursions.
--
--   **Formalization Note** $V^{\mathbb G}_0$ is $\mathcal G_0$-measurable but not constant in general, so "solving the dual problem" is read as the equality of its expectation with the dual bound, in the extended reals. $V^{\mathbb G}_0(a)$ does not depend on $a$; the statement quantifies over all action sequences.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, §2.3, eq. (10) and the preceding paragraph

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework
import Definitions.Def_InfoRelax_RelaxOrder_RecursiveModel
import Definitions.Def_InfoRelax_RelaxOrder_Penalty

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-- **§2.3, eq. (10)**, Brown, Smith & Sun (2010), Oper. Res., DOI 10.1287/opre.1090.0796, p. 5.

In the recursive setting, let `𝔾` be a relaxation of `𝔽`, `w` generating functions as in
Proposition 2.2 and `z = ∑_t z_t`, `z_t(a) = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | 𝓕_t]`, the penalty it
constructs. The dual value functions `V^𝔾_t` of (10) (the recursion (2) with rewards `r_t − z_t`
and conditional expectations given `𝒢_t`, `V^𝔾_{T+1} = 0`) solve the dual problem:
`𝔼[V^𝔾_0] = sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)]`.

**Formalization Note.** `V^𝔾_0` is `𝒢_0`-measurable but not constant in general, so "solving the
dual problem" is read as the equality of its expectation with the dual bound. `V^𝔾_0(a)` does
not depend on `a`; the statement quantifies over all `a`. Pinned: countable action type with the
discrete σ-algebra, bounded period rewards, generating functions as in `GeneratingFns`. -/
theorem eq_10_dual_recursion {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : InfoRelax.IdealPenalty.IsRelaxation M.𝔽 𝔾)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (hw : GeneratingFns μ w) :
    ∀ a : Fin (T + 1) → X,
      ((∫ ω, dualValueFn M μ 𝔾 w 0 a ω ∂μ : ℝ) : EReal) =
        InfoRelax.IdealPenalty.dualBound μ M.A 𝔾 M.r (penalty μ M.𝔽 𝔾 w) := by sorry

end InfoRelax.RelaxOrder
