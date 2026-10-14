-- Prove2me | Theorems.Thm_HighUncertHT_Game_lemma_3
-- name    : HighUncertHT.Game.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:17.857654+00:00
-- url     : https://prove2.me/theorems/fb5a3ace-5e7b-4acc-858d-5f63bff32a2d
-- title:
--   Lemma 3, p. 17 — 𝔼‖Ŵ^{tot,n}‖²_t, 𝔼‖Q̂^{tot,n}‖²_t ≤ c(t+1)²
-- statement:
--   There exists a constant $c<\infty$, depending only on the setting, such that for all $n\ge1$, $t\ge0$, admissible controls $a^n\in\mathcal A^n$ and admissible strategies $\beta^n\in\mathbb B^n$,
--   $$
--   \mathbb E\big[\|\hat W^{\mathrm{tot},n}\|_t^2\big]\le c(t+1)^2,\qquad
--   \mathbb E\big[\|\hat Q^{\mathrm{tot},n}\|_t^2\big]\le c(t+1)^2,
--   $$
--   where $\|f\|_t=\sup_{0\le s\le t}|f(s)|$.
--
--   These polynomial moment bounds give uniform integrability of the scaled holding cost, which is used to pass from convergence of processes to convergence of costs.
--
--   **Formalization Note** The constant is chosen after the setting and before $n$, $t$, the control and the strategy. The expectations are lower Lebesgue integrals of quantities in $[0,\infty]$.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 17, Lemma 3

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Control

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Lemma 3, p. 17: there is a constant `c < ∞` (depending only on the model) such that for all
`n ≥ 1`, `t ≥ 0`, controls `aⁿ` and admissible strategies `βⁿ`,
`𝔼‖Ŵ^{tot,n}‖²_t ≤ c(t + 1)²` and `𝔼‖Q̂^{tot,n}‖²_t ≤ c(t + 1)²`. -/
theorem lemma_3 {L : ℕ} (S : Setting L) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → ∀ f : AdversaryControl S n,
      ∀ β ∈ admissibleStrategies S n,
        (∫⁻ ω, supNorm (fun s => scaledTotalWorkload n (f.ctrlPath ω) (β (f.ctrlPath ω)) s) t ^ 2
            ∂f.law ≤ ENNReal.ofReal (c * (t + 1) ^ 2)) ∧
        (∫⁻ ω, supNorm (fun s => scaledTotalQueue n (f.ctrlPath ω) (β (f.ctrlPath ω)) s) t ^ 2
            ∂f.law ≤ ENNReal.ofReal (c * (t + 1) ^ 2)) := by sorry

end HighUncertHT.Game
