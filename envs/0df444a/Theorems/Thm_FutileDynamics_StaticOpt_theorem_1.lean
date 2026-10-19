-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_theorem_1
-- name    : FutileDynamics.StaticOpt.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:48.243982+00:00
-- url     : https://prove2.me/theorems/3ebe791b-b0b5-4abf-afc2-d68f7dfff492
-- title:
--   Theorem 1, pp. 11–12 — minimax regret is T times the single-round minimax regret over point masses; repeated direct static mechanisms are (near-)optimal
-- statement:
--   Let $\mathcal F\subseteq\Delta(\Theta)$ satisfy Assumption 1 (every point mass $\delta_\theta$ is in $\mathcal F$) and Assumption 2 ($\mathrm{OPT}(F,T)\le\mathbb E_{\theta\sim F}[\mathrm{OPT}(\delta_\theta,T)]$ for $F\in\mathcal F$). Then:
--
--   1. the minimax regret of the $T$-round problem is
--   $$\mathrm{Regret}(T)=T\cdot\inf_{S\in\mathcal S^{\times1}}\sup_{\theta\in\Theta}\mathrm{Regret}(S,\delta_\theta,1);$$
--   2. for every $\epsilon\ge0$, if $S\in\mathcal S^{\times1}$ satisfies
--   $$\sup_{\theta\in\Theta}\mathrm{Regret}(S,\delta_\theta,1)\le\inf_{S'\in\mathcal S^{\times1}}\sup_{\theta\in\Theta}\mathrm{Regret}(S',\delta_\theta,1)+\frac{\epsilon}{T},\qquad(1)$$
--   then its repetition satisfies $\sup_{F\in\mathcal F}\mathrm{Regret}(S^{\times T},F,T)\le\mathrm{Regret}(T)+\epsilon$;
--   3. $\arg\min_{A\in\mathcal A}\sup_{F\in\mathcal F}\mathrm{Regret}(A,F,T)$ is empty if and only if $\arg\min_{S\in\mathcal S^{\times1}}\sup_{\theta}\mathrm{Regret}(S,\delta_\theta,1)$ is empty.
--
--   The theorem says dynamics are futile for robust (minimax-regret) mechanism design. Neither history dependence nor learning about $F$ lowers the worst-case regret, and repeating a (near-)optimal single-round mechanism is (near-)optimal.
--
--   **Formalization Note** Part 3 is stated in the equivalent form "a minimizer exists iff a minimizer exists"; a minimizer is an element whose value equals the infimum. $\mathcal A$ ranges over all IC dynamic mechanisms with arbitrary report spaces. IC is required against every distribution and every feasible deviation. Disclosed conventions: $u,v$ bounded and jointly measurable; $\Theta$ standard Borel and nonempty; rules and strategies measurable (strategies jointly in $F$); $0<T$; rounds 0-indexed.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), pp. 11–12, Theorem 1

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Theorem 1** (Balseiro–Kim–Russo, pp. 11–12). Under Assumptions 1 and 2:
(1) `Regret(T) = T · inf_{S ∈ S^{×1}} sup_θ Regret(S, δ_θ, 1)`;
(2) for every `ε ≥ 0`, if `S ∈ S^{×1}` satisfies (1), i.e.
`sup_θ Regret(S, δ_θ, 1) ≤ inf_{S'} sup_θ Regret(S', δ_θ, 1) + ε / T`, then
`sup_{F ∈ 𝓕} Regret(S^{×T}, F, T) ≤ Regret(T) + ε`;
(3) `argmin_{A ∈ 𝒜} sup_F Regret(A, F, T)` is nonempty iff `argmin_{S ∈ S^{×1}} sup_θ Regret(S, δ_θ, 1)` is
nonempty (the page: "empty iff empty"); a minimizer is an element whose value equals the infimum.
Conventions (disclosed): bounded measurable `u, v`; `Θ` standard Borel and nonempty; measurable rules and
strategies; `0 < T`. -/
theorem theorem_1 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) (T : ℕ) (hT : 0 < T)
    (h1 : Assumption1 𝓕) (h2 : Assumption2 G 𝓕 T) :
    minimaxRegret G 𝓕 T = T * singleRoundValue G ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ d : DirectRule G, SingleRoundIC G d →
      (⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1) ≤ singleRoundValue G + ε / T →
      worstRegret G (repeatDirect G d) 𝓕 T ≤ minimaxRegret G 𝓕 T + ε) ∧
    ((∃ A : DynMech Θ Ω, IsIC G A T ∧ worstRegret G A 𝓕 T = minimaxRegret G 𝓕 T) ↔
      (∃ d : DirectRule G, SingleRoundIC G d ∧
        (⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1) = singleRoundValue G)) := by sorry

end FutileDynamics.StaticOpt
