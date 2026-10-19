-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_lemma_6
-- name    : FutileDynamics.StaticOpt.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:39.601979+00:00
-- url     : https://prove2.me/theorems/b8b65322-fb31-4733-94cf-495985245a5f
-- title:
--   Lemma 6, p. ec 6 — for S ∈ S×1, sup_F {E_F[OPT(δθ,1)] − PrincipalUtility(S,F,1)} ≤ sup_θ Regret(S, δθ, 1)
-- statement:
--   For every single-round direct IC/IR mechanism $S\in\mathcal S^{\times1}$,
--   $$\sup_{F\in\mathcal F}\Big\{\mathbb E_{\theta\sim F}[\mathrm{OPT}(\delta_\theta,1)]-\mathrm{PrincipalUtility}(S,F,1)\Big\}\le\sup_{\theta\in\Theta}\mathrm{Regret}(S,\delta_\theta,1).$$
--
--   This is the single-round half of the upper bound: against the point-mass benchmark, mixtures are no worse for the principal than point masses.
--
--   **Formalization Note** $\mathcal F$ is any set of probability measures. If it is empty, the left side is $\sup\emptyset=0$ in Lean; the right side is nonnegative, so the statement stays true. $\mathbb E_{\theta\sim F}$ is a Bochner integral. It is $0$ if $\theta\mapsto\mathrm{OPT}(\delta_\theta,1)$ is not measurable, and since $\mathrm{OPT}\ge0$ the inequality still holds then. Assumed: $\Theta$ standard Borel and nonempty, and the model conventions.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. ec 6, Lemma 6

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Lemma 6** (p. ec 6): for any `S ∈ S^{×1}`,
`sup_{F ∈ 𝓕} {E_{θ∼F}[OPT(δ_θ, 1)] − PrincipalUtility(S, F, 1)} ≤ sup_θ Regret(S, δ_θ, 1)`. -/
theorem lemma_6 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) :
    ∀ d : DirectRule G, SingleRoundIC G d →
      sSup ((fun F => (∫ θ, OPT G (Measure.dirac θ) 1 ∂F) -
          principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1) '' 𝓕) ≤
        ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1 := by sorry

end FutileDynamics.StaticOpt
