-- Prove2me | Theorems.Thm_HighUncertHT_Game_theorem_1
-- name    : HighUncertHT.Game.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:18.718105+00:00
-- url     : https://prove2.me/theorems/3452a975-39b8-4e85-80b7-e66f6369a59b
-- title:
--   Theorem 1, p. 9 — the nonpreemptive cµ policy is asymptotically optimal against any adversary
-- statement:
--   Consider an arbitrary sequence of controls for the adversary, $a^n\in\mathcal A^n$. Then the cost of the nonpreemptive cµ strategy is finite for every $n\ge1$, and
--   $$
--   \lim_{n\to\infty}\Big\{\inf_{\beta^n\in\mathbb B^n}C^n(\beta^n(a^n),a^n)-C^n(\beta^{*n}(a^n),a^n)\Big\}=0 .
--   $$
--
--   The scheduler can therefore commit to $\beta^{*n}$ without knowing how the adversary behaves, and the asymptotic analysis of the game reduces to a control problem for the adversary alone.
--
--   **Formalization Note** Costs are in $[0,\infty]$; the finiteness of $C^n(\beta^{*n}(a^n),a^n)$ (a consequence of Lemma 3) makes the difference of real parts the paper's difference, and the infimum is then finite as well since $\beta^{*n}\in\mathbb B^n$.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 9, Theorem 1

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Control
import Definitions.Def_HighUncertHT_Game_Priority

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 1, p. 9: the nonpreemptive cµ strategy is asymptotically optimal against every
adversary. For every sequence of controls `aⁿ ∈ 𝒜ⁿ`, the cost of `β^{*n}` is finite and
`lim_n {inf_{βⁿ ∈ 𝔹ⁿ} Cⁿ(βⁿ(aⁿ), aⁿ) - Cⁿ(β^{*n}(aⁿ), aⁿ)} = 0`. -/
theorem theorem_1 {L : ℕ} (S : Setting L) (f : (n : ℕ) → AdversaryControl S n) :
    (∀ n : ℕ, 1 ≤ n → cost S n (betaStar S n) (f n) ≠ ⊤) ∧
    Tendsto (fun n => (⨅ β ∈ admissibleStrategies S n, cost S n β (f n)).toReal -
        (cost S n (betaStar S n) (f n)).toReal) atTop (𝓝 0) := by sorry

end HighUncertHT.Game
