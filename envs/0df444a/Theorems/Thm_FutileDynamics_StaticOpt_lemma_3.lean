-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_lemma_3
-- name    : FutileDynamics.StaticOpt.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:39.145022+00:00
-- url     : https://prove2.me/theorems/09fef158-6f3f-4813-b4d5-f5a31e25d7ae
-- title:
--   Lemma 3 (Upper Bound), p. 15 — under Assumption 2, every S ∈ S×1 has sup_F Regret(S×T, F, T) ≤ T·sup_θ Regret(S, δθ, 1)
-- statement:
--   Suppose Assumption 2 holds: $\mathrm{OPT}(F,T)\le\mathbb E_{\theta\sim F}[\mathrm{OPT}(\delta_\theta,T)]$ for all $F\in\mathcal F$. Then every single-round direct IC/IR mechanism $S\in\mathcal S^{\times1}$ satisfies
--   $$\sup_{F\in\mathcal F}\mathrm{Regret}(S^{\times T},F,T)\le T\cdot\sup_{\theta\in\Theta}\mathrm{Regret}(S,\delta_\theta,1).\qquad(5)$$
--
--   Taking infima gives the upper bound $\mathrm{Regret}(T)\le T\cdot\inf_{S}\sup_\theta\mathrm{Regret}(S,\delta_\theta,1)$.
--
--   **Formalization Note** Assumption 2's expectation is a Bochner integral, which is $0$ for a non-measurable integrand. That only strengthens the hypothesis, and no integrability clause is added. Assumed: $0<T$, $\Theta$ standard Borel and nonempty, every $F\in\mathcal F$ a probability measure, and the model conventions.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. 15, Lemma 3, (5)

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Lemma 3** (Upper Bound, p. 15): under Assumption 2, for every `S ∈ S^{×1}`,
`sup_{F ∈ 𝓕} Regret(S^{×T}, F, T) ≤ T · sup_θ Regret(S, δ_θ, 1)` (5). -/
theorem lemma_3 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) (T : ℕ) (hT : 0 < T) (h2 : Assumption2 G 𝓕 T) :
    ∀ d : DirectRule G, SingleRoundIC G d →
      worstRegret G (repeatDirect G d) 𝓕 T ≤
        T * ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1 := by sorry

end FutileDynamics.StaticOpt
