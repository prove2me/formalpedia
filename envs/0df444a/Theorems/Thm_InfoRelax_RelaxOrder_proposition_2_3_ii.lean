-- Prove2me | Theorems.Thm_InfoRelax_RelaxOrder_proposition_2_3_ii
-- name    : InfoRelax.RelaxOrder.proposition_2_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:07.265868+00:00
-- url     : https://prove2.me/theorems/5615576e-068b-443d-8f0a-273d0154d051
-- title:
--   Proposition 2.3(ii) — close penalties give close dual bounds
-- statement:
--   Let the feasible set $A$ be nonempty, let $\mathbb E[r(\alpha)]$ exist for every policy $\alpha$, let $\mathbb G$ be an information relaxation of $\mathbb F$, and let $z^1,z^2\in\mathcal Z_{\mathbb F}$ be two dual feasible penalties. Write
--   $$D_i=\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E\big[r(\alpha_G)-z^i(\alpha_G)\big],\qquad i=1,2,$$
--   and assume that $D_1$ and $D_2$ are not both $+\infty$. Then
--   $$\inf_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E\big[z^2(\alpha_G)-z^1(\alpha_G)\big]\le D_1-D_2\le\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E\big[z^2(\alpha_G)-z^1(\alpha_G)\big].\qquad(13)$$
--
--   This is a continuity property of the dual bound in the penalty: if $\mathbb E[z^2(\alpha_G)-z^1(\alpha_G)]$ is small for every $\alpha_G$, the two bounds are close. With $z^2$ the ideal penalty, it bounds how far the bound of any other penalty $z^1$ can exceed the optimal bound.
--
--   **Formalization Note** All quantities are in the extended reals. The page's difference $D_1-D_2$ is undefined when both bounds are $+\infty$, and in Lean's extended reals $+\infty-(+\infty)=-\infty$, which would make the left inequality false; the hypothesis excludes exactly that case. Exactly one infinite bound is allowed, with $\pm\infty-c=\pm\infty$.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 6, Proposition 2.3(ii), eq. (13)

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-- **Proposition 2.3(ii)**, Brown, Smith & Sun (2010), Oper. Res., DOI 10.1287/opre.1090.0796,
p. 6, eq. (13).

For any two dual feasible penalties `z¹, z² ∈ 𝒵_𝔽` and any information relaxation `𝔾` of `𝔽`,
writing `D_i = sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z^i(α_G)]`,
`inf_{α_G ∈ 𝒜_𝔾} 𝔼[z²(α_G) − z¹(α_G)] ≤ D_1 − D_2 ≤ sup_{α_G ∈ 𝒜_𝔾} 𝔼[z²(α_G) − z¹(α_G)]`.

**Formalization Note.** General setting of §2.1–§2.2: any feasible set `A` (nonempty) and any total
reward `r` whose expectation exists along every policy. All four quantities are in `EReal`. The
page's difference `D_1 − D_2` is undefined when both bounds are `+∞`; in `EReal`, `⊤ − ⊤ = ⊥`,
which would make the left inequality false. The hypothesis `hfin` excludes exactly that case
(at least one of the two bounds is finite). Both bounds exceed `−∞` because `A` is nonempty. -/
theorem proposition_2_3_ii {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set (Fin (T + 1) → X)) (hA : A.Nonempty)
    (r : (Fin (T + 1) → X) → Ω → ℝ) (hr : InfoRelax.IdealPenalty.RewardIntegrable μ A r)
    (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : InfoRelax.IdealPenalty.IsRelaxation 𝔽 𝔾)
    (z₁ z₂ : (Fin (T + 1) → X) → Ω → ℝ) (hz₁ : z₁ ∈ InfoRelax.IdealPenalty.dualFeasible μ A 𝔽)
    (hz₂ : z₂ ∈ InfoRelax.IdealPenalty.dualFeasible μ A 𝔽)
    (hfin : InfoRelax.IdealPenalty.dualBound μ A 𝔾 r z₁ ≠ ⊤ ∨ InfoRelax.IdealPenalty.dualBound μ A 𝔾 r z₂ ≠ ⊤) :
    infValue μ (InfoRelax.IdealPenalty.adaptedPolicies A 𝔾) (fun a ω => z₂ a ω - z₁ a ω) ≤
        InfoRelax.IdealPenalty.dualBound μ A 𝔾 r z₁ - InfoRelax.IdealPenalty.dualBound μ A 𝔾 r z₂ ∧
      InfoRelax.IdealPenalty.dualBound μ A 𝔾 r z₁ - InfoRelax.IdealPenalty.dualBound μ A 𝔾 r z₂ ≤
        InfoRelax.IdealPenalty.supValue μ (InfoRelax.IdealPenalty.adaptedPolicies A 𝔾) (fun a ω => z₂ a ω - z₁ a ω) := by sorry

end InfoRelax.RelaxOrder
