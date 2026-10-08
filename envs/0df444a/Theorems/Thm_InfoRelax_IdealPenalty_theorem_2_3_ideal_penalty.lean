-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_theorem_2_3_ideal_penalty
-- name    : InfoRelax.IdealPenalty.theorem_2_3_ideal_penalty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:40.428584+00:00
-- url     : https://prove2.me/theorems/13da274a-b819-4eee-a079-05aba2fd21db
-- title:
--   Theorem 2.3 (The Ideal Penalty)
-- statement:
--   Consider a dynamic program in recursive form: a natural filtration $\mathbb F$ with $\mathcal F_0=\{\emptyset,\Omega\}$, a countable action set, nonempty feasible-action sets $A_t(a_0,\dots,a_{t-1})$, and bounded period rewards $r_t(a_0,\dots,a_t)$ that are $\mathcal F_t$-measurable, with total reward $r=\sum_t r_t$ and value functions $V_t$ given by (2). Let $\mathbb G$ be a relaxation of $\mathbb F$ and let $z^\star$ be the penalty of Proposition 2.2 for the generating functions $w_t(a)=V_{t+1}(a_0,\dots,a_t)$:
--   $$z^\star(a)=\sum_{t=0}^T\Big(\mathbb E[V_{t+1}(a)\mid\mathcal G_t]-\mathbb E[V_{t+1}(a)\mid\mathcal F_t]\Big).$$
--   Then:
--   1. $z^\star$ is dual feasible, $z^\star\in\mathcal Z_{\mathbb F}$;
--   2. $z^\star$ is optimal:
--   $$\sup_{\alpha_F\in\mathcal A_{\mathbb F}}\mathbb E[r(\alpha_F)]=\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z^\star(\alpha_G)];\qquad(11)$$
--   3. if $\alpha^*_F\in\mathcal A_{\mathbb F}$ attains the supremum on the left of (11), then $\alpha^*_F$ also attains the supremum on the right;
--   4. if $\mathbb G$ is the perfect-information relaxation ($\mathcal G_t=\mathcal F$ for all $t$) and $\alpha^*_F\in\mathcal A_{\mathbb F}$ is an optimal policy, then $r(\alpha^*_F)-z^\star(\alpha^*_F)=\mathbb E[r(\alpha^*_F)]$ almost surely.
--
--   The ideal penalty closes the duality gap for every information relaxation at once; in the perfect-information case it even removes all randomness from the penalized reward of an optimal policy. It is the target that practical penalties built from approximate value functions try to approximate.
--
--   **Formalization Note** $z^\star$ and the value functions are definitions computed from the data of the DP, not variables constrained by hypotheses. Values are extended reals. The countable action set and bounded rewards are pinned regularity assumptions.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, Theorem 2.3, eq. (11)

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **Theorem 2.3 (The Ideal Penalty)**, Brown, Smith & Sun (2010), Oper. Res., DOI
10.1287/opre.1090.0796, p. 5, eq. (11).

In the recursive setting, let `𝔾` be a relaxation of `𝔽` and let `z⋆` be the penalty of
Proposition 2.2 for `w_t(a) = V_{t+1}(a_0, …, a_t)`. Then
1. `z⋆` is dual feasible;
2. `z⋆` is optimal: `sup_{α_F ∈ 𝒜_𝔽} 𝔼[r(α_F)] = sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z⋆(α_G)]` (11);
3. if `α*_F ∈ 𝒜_𝔽` attains the primal supremum, it also attains the supremum on the right of (11);
4. if `𝔾` is the perfect-information relaxation and `α*_F ∈ 𝒜_𝔽` is optimal, then
   `r(α*_F) − z⋆(α*_F) = 𝔼[r(α*_F)]` almost surely.

**Formalization Note.** `z⋆` is the def `idealPenalty`, built from the def `valueFn` (the
recursion (2)); nothing is a free variable. Values in `EReal`. Recursive setting
(`RecursiveDP.Valid`: `𝓕_0 = {∅, Ω}`, nonempty feasible sets depending on past actions,
`𝓕_t`-measurable bounded period rewards depending on `a_0, …, a_t`); pinned countable action type
with the discrete σ-algebra. "Perfect information" is `𝔾 = perfectInfo` (`𝒢_t = 𝓕` for all `t`). -/
theorem theorem_2_3_ideal_penalty {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : IsRelaxation M.𝔽 𝔾) :
    idealPenalty M μ 𝔾 ∈ dualFeasible μ M.A M.𝔽 ∧
      primalValue μ M.A M.𝔽 M.r = dualBound μ M.A 𝔾 M.r (idealPenalty M μ 𝔾) ∧
      (∀ α ∈ adaptedPolicies M.A M.𝔽,
        ((∫ ω, M.r (α ω) ω ∂μ : ℝ) : EReal) = primalValue μ M.A M.𝔽 M.r →
          ((∫ ω, (M.r (α ω) ω - idealPenalty M μ 𝔾 (α ω) ω) ∂μ : ℝ) : EReal) =
            dualBound μ M.A 𝔾 M.r (idealPenalty M μ 𝔾)) ∧
      (𝔾 = perfectInfo →
        ∀ α ∈ adaptedPolicies M.A M.𝔽,
          ((∫ ω, M.r (α ω) ω ∂μ : ℝ) : EReal) = primalValue μ M.A M.𝔽 M.r →
            ∀ᵐ ω ∂μ, M.r (α ω) ω - idealPenalty M μ 𝔾 (α ω) ω = ∫ ω', M.r (α ω') ω' ∂μ) := by sorry

end InfoRelax.IdealPenalty
