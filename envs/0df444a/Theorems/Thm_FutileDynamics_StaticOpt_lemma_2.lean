-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_lemma_2
-- name    : FutileDynamics.StaticOpt.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:23.444434+00:00
-- url     : https://prove2.me/theorems/58def75e-654b-4f3b-8282-12e47a7ae1d7
-- title:
--   Lemma 2 (Lower Bound), p. 15 — under Assumption 1, every IC A has some S ∈ S×1 with sup_F Regret(A, F, T) ≥ T·sup_θ Regret(S, δθ, 1)
-- statement:
--   Suppose $\mathcal F\subseteq\Delta(\Theta)$ contains every point mass (Assumption 1). For every incentive compatible dynamic mechanism $A$ there is a single-round direct IC/IR mechanism $S\in\mathcal S^{\times1}$ with
--   $$\sup_{F\in\mathcal F}\mathrm{Regret}(A,F,T)\ge T\cdot\sup_{\theta\in\Theta}\mathrm{Regret}(S,\delta_\theta,1).\qquad(4)$$
--
--   Taking infima gives the lower bound $\mathrm{Regret}(T)\ge T\cdot\inf_{S\in\mathcal S^{\times1}}\sup_\theta\mathrm{Regret}(S,\delta_\theta,1)$.
--
--   **Formalization Note** The quantifier order is the page's: for every $A$ there exists $S$. Assumed: $0<T$, $\Theta$ standard Borel and nonempty, every $F\in\mathcal F$ a probability measure, and the model conventions.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. 15, Lemma 2, (4)

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Lemma 2** (Lower Bound, p. 15): under Assumption 1, for every incentive compatible dynamic mechanism
`A` there is `S ∈ S^{×1}` with `sup_{F ∈ 𝓕} Regret(A, F, T) ≥ T · sup_θ Regret(S, δ_θ, 1)` (4). -/
theorem lemma_2 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) (T : ℕ) (hT : 0 < T) (h1 : Assumption1 𝓕) :
    ∀ A : DynMech Θ Ω, IsIC G A T → ∃ d : DirectRule G, SingleRoundIC G d ∧
      T * (⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1) ≤ worstRegret G A 𝓕 T := by sorry

end FutileDynamics.StaticOpt
