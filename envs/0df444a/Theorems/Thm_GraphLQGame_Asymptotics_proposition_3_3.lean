-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_proposition_3_3
-- name    : GraphLQGame.Asymptotics.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:14.72329+00:00
-- url     : https://prove2.me/theorems/114f7ad4-dcad-4c03-ab4f-4bb9236adfd9
-- title:
--   Proposition 3.3 (first claim) — $f_\mu$ is strictly increasing and concave with $0<f_\mu'\le c$
-- statement:
--   Let $c>0$ and $\mu\in\mathcal P_{\mathrm{Lap}}$, and let $f_\mu:\mathbb R_+\to\mathbb R_+$ solve
--   $$f_\mu'(t) = c\,Q_\mu'(f_\mu(t)),\quad t>0,\qquad f_\mu(0) = 0.$$
--   Then $f_\mu$ is strictly increasing and concave on $\mathbb R_+$, and
--   $$0 < f_\mu'(t)\le c\qquad\text{for all } t\ge0.$$
--
--   Monotonicity of $f$ is used in the correlation-decay estimate (Proposition 2.12) and in bounding the equilibrium variances.
--
--   **Formalization Note** At $t = 0$ the derivative is the right derivative (within $\mathbb R_+$). The second sentence of Proposition 3.3 (about $V_\mu(0)$, $V_\mu'(0)$, $V_\mu''(0)$) is not part of this item.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Proposition 3.3, first sentence, p. 21

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Asymptotics_Spectral
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace GraphLQGame.Asymptotics

/-- **Proposition 3.3**, first sentence, Lacker–Soret, arXiv:2005.14102v2, §3, p. 21.

For each `μ ∈ 𝒫_Lap`, the solution `f_μ : ℝ₊ → ℝ₊` of `f' = c Q'_μ(f)`, `f(0) = 0` (Proposition 3.2)
is strictly increasing and concave on `ℝ₊`, with `0 < f'_μ(t) ≤ c` for all `t ≥ 0`.

Formalization Note: `f_μ` is any solution in the sense of Proposition 3.2 (`IsODESolRplus`). At
`t = 0` the derivative is the right derivative (derivative within `ℝ₊`). `c > 0` is the paper's
standing assumption (§2.1). -/
theorem proposition_3_3 {c : ℝ} (hc : 0 < c) (μ : Measure ℝ) (hμ : GraphLQGame.Equilibrium.IsPLap μ) (f : ℝ → ℝ)
    (hf : GraphLQGame.Equilibrium.IsODESolRplus c (GraphLQGame.Equilibrium.Qmu μ) f) :
    StrictMonoOn f (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) f ∧
      ∀ t : ℝ, 0 ≤ t → ∃ d : ℝ, HasDerivWithinAt f d (Set.Ici 0) t ∧ 0 < d ∧ d ≤ c := by sorry

end GraphLQGame.Asymptotics
