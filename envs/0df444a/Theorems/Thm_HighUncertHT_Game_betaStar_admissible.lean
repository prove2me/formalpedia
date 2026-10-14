-- Prove2me | Theorems.Thm_HighUncertHT_Game_betaStar_admissible
-- name    : HighUncertHT.Game.betaStar_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:19.56098+00:00
-- url     : https://prove2.me/theorems/4a0fec65-b82d-4af2-b13e-796cbe97fc87
-- title:
--   §2.2, p. 9 — the nonpreemptive cµ strategy is admissible: β*ⁿ ∈ 𝔹ⁿ
-- statement:
--   For every setting and every $n\ge1$, the nonpreemptive cµ strategy $\beta^{*n}$ (priority to the type with the largest $h^\ell\mu^\ell$) is an admissible strategy of the $n$-th system:
--   $$
--   \beta^{*n}\in\mathbb B^n .
--   $$
--   That is, $\beta^{*n}$ is measurable, maps every control path of $\underline{\mathcal A}^n$ into $\mathrm{Lip}(\mathrm{Sim})$, and satisfies the nonnegativity constraint (9), work conservation (12) and causality (13).
--
--   The paper asserts this in the sentence introducing $\beta^{*n}$. It guarantees that $\mathbb B^n$ is nonempty, so that the game value $V^n$ and the infimum in Theorem 1 are not taken over an empty set.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 9, §2.2 ("We will denote by β*ⁿ ∈ 𝔹ⁿ the strategy corresponding to the nonpreemptive cµ policy")

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Priority

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- §2.2, p. 9: the nonpreemptive cµ strategy (priority to the highest index, see
`Def_HighUncertHT_Game_Priority`) is admissible for every system `n ≥ 1`: `β^{*n} ∈ 𝔹ⁿ`. -/
theorem betaStar_admissible {L : ℕ} (S : Setting L) (n : ℕ) (hn : 1 ≤ n) :
    betaStar S n ∈ admissibleStrategies S n := by sorry

end HighUncertHT.Game
