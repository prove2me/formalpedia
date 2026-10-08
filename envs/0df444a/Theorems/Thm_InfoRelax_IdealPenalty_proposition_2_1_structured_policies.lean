-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_proposition_2_1_structured_policies
-- name    : InfoRelax.IdealPenalty.proposition_2_1_structured_policies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:37.618675+00:00
-- url     : https://prove2.me/theorems/007889ea-6b70-409b-b7e1-f5b71d513446
-- title:
--   Proposition 2.1 (Structured Policies)
-- statement:
--   Let $\mathbb G$ be a relaxation of $\mathbb F$, let $A$ be nonempty, assume $\mathbb E[r(\alpha)]$ exists for every policy, and let $\mathcal S\subseteq\mathcal A$ be a set of policies with $\mathcal S_{\mathbb F}=\mathcal S\cap\mathcal A_{\mathbb F}$ and $\mathcal S_{\mathbb G}=\mathcal S\cap\mathcal A_{\mathbb G}$. If
--   $$\sup_{\alpha_F\in\mathcal A_{\mathbb F}}\mathbb E[r(\alpha_F)]=\sup_{\alpha_F\in\mathcal S_{\mathbb F}}\mathbb E[r(\alpha_F)],$$
--   then for every dual feasible $z\in\mathcal Z_{\mathbb F}$,
--   $$\sup_{\alpha_F\in\mathcal A_{\mathbb F}}\mathbb E[r(\alpha_F)]\le\sup_{\alpha_G\in\mathcal S_{\mathbb G}}\mathbb E[r(\alpha_G)-z(\alpha_G)]\le\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z(\alpha_G)].\qquad(9)$$
--   Moreover, both inequalities hold for every penalty $z\in\mathcal Z$ with $\mathbb E[z(\alpha_F)]\le0$ for all $\alpha_F\in\mathcal S_{\mathbb F}$.
--
--   When the primal problem is known to have an optimal policy of a given structure, the dual problem may be restricted to policies of the same structure, giving a bound that is at least as tight.
--
--   **Formalization Note** The page uses $\mathcal S_{\mathbb F}$ and $\mathcal S_{\mathbb G}$ without defining them; they are read as the intersections above. In the "moreover" clause $z$ still lies in the penalty set $\mathcal Z$, so its expectations exist. Values are extended reals.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, Proposition 2.1, eq. (9)

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **Proposition 2.1 (Structured Policies)**, Brown, Smith & Sun (2010), Oper. Res., DOI
10.1287/opre.1090.0796, p. 5, eq. (9).

If for some `𝒮 ⊆ 𝒜` we have `sup_{α_F ∈ 𝒜_𝔽} 𝔼[r(α_F)] = sup_{α_F ∈ 𝒮_𝔽} 𝔼[r(α_F)]`, then for any
dual feasible `z`,
`sup_{α_F ∈ 𝒜_𝔽} 𝔼[r(α_F)] ≤ sup_{α_G ∈ 𝒮_𝔾} 𝔼[r(α_G) − z(α_G)] ≤ sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)]`.
Moreover the inequalities also hold for all `z` with `𝔼[z(α_F)] ≤ 0` for all `α_F ∈ 𝒮_𝔽`.

**Formalization Note.** The page uses `𝒮_𝔽`, `𝒮_𝔾` without defining them; they are read as
`𝒮 ∩ 𝒜_𝔽` and `𝒮 ∩ 𝒜_𝔾`. The page's `𝔾` is a relaxation of `𝔽` (the standing setting of
§2.2). In the "moreover" clause `z` still lies in the penalty set `𝒵` (its expectations exist);
only the feasibility condition is weakened. General framework; values in `EReal`. -/
theorem proposition_2_1_structured_policies {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (hA : A.Nonempty) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (r : (Fin (T + 1) → X) → Ω → ℝ) (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾)
    (S : Set (Ω → Fin (T + 1) → X)) (hS : S ⊆ policies A)
    (hSopt : primalValue μ A 𝔽 r = supValue μ (S ∩ adaptedPolicies A 𝔽) r) :
    (∀ z ∈ dualFeasible μ A 𝔽,
        primalValue μ A 𝔽 r ≤
            supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ∧
          supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ≤
            dualBound μ A 𝔾 r z) ∧
      (∀ z ∈ penalties μ A,
        (∀ α ∈ S ∩ adaptedPolicies A 𝔽, ∫ ω, z (α ω) ω ∂μ ≤ 0) →
          primalValue μ A 𝔽 r ≤
              supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ∧
            supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ≤
              dualBound μ A 𝔾 r z) := by sorry

end InfoRelax.IdealPenalty
