-- Prove2me | Theorems.Thm_HighUncertHT_Game_lemma_2
-- name    : HighUncertHT.Game.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:09.781965+00:00
-- url     : https://prove2.me/theorems/e6cfdba2-de3e-496b-a68d-cf8ced9f7539
-- title:
--   Lemma 2, p. 17 — the total workload does not depend on the strategy
-- statement:
--   Let $n\ge1$, let $a^n\in\mathcal A^n$ be an admissible control of the adversary, and let $\beta^n,\tilde\beta^n\in\mathbb B^n$ be admissible strategies. If $W^{\mathrm{tot},n}$ and $\tilde W^{\mathrm{tot},n}$ are the total workload processes corresponding to $(a^n,\beta^n)$ and $(a^n,\tilde\beta^n)$, then almost surely
--   $$
--   W^{\mathrm{tot},n}_t=\tilde W^{\mathrm{tot},n}_t\qquad\text{for all }t\ge0 .
--   $$
--
--   Under work conservation the total workload is the reflection of the netput $A^{\mathrm{tot},n}-n\,\mathrm{id}$, so the scheduler can only redistribute the workload among types. This is what reduces the game to the choice of the composition of the workload.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 17, Lemma 2

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Control

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Lemma 2, p. 17: the total workload does not depend on the strategy. For a control `aⁿ` and
two admissible strategies `βⁿ, β̃ⁿ`, the processes `W^{tot,n}` they produce coincide (almost
surely, at every time `t ≥ 0`). -/
theorem lemma_2 {L : ℕ} (S : Setting L) (n : ℕ) (hn : 1 ≤ n) (f : AdversaryControl S n)
    (β β' : ControlPath L → EffortPath L)
    (hβ : β ∈ admissibleStrategies S n) (hβ' : β' ∈ admissibleStrategies S n) :
    ∀ᵐ ω ∂f.law, ∀ t : ℝ, 0 ≤ t →
      ∑ ℓ, workload n (f.ctrlPath ω) (β (f.ctrlPath ω)) t ℓ =
        ∑ ℓ, workload n (f.ctrlPath ω) (β' (f.ctrlPath ω)) t ℓ := by sorry

end HighUncertHT.Game
