-- Prove2me | Theorems.Thm_OnlineRandomization_Tightness_params_tendsto
-- name    : OnlineRandomization.Tightness.params_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:33:55.212368+00:00
-- url     : https://prove2.me/theorems/cbd12063-d95d-43d1-b1c0-7b6e92ff9b05
-- title:
--   §2, p. 12 — as $t \to \infty$, $m(t) \to \beta$ and $M(t) \to \alpha\beta$
-- statement:
--   Let $\alpha, \beta > 0$, and let $m(t)$ and $M(t)$ be the solutions of the equations $\beta = \frac{(2t-2)m + M + 1}{2t}$, $\alpha = \frac{1 + (2t-1)M}{2 + (2t-2)m}$, namely
--   $$
--   m(t) = \frac{1 + (2t-1)(2t\beta - 1) - 2\alpha}{(2t-2)(\alpha + 2t - 1)}, \qquad M(t) = \frac{2t\alpha\beta + \alpha - 1}{\alpha + 2t - 1}.
--   $$
--   Then, as the integer $t$ tends to infinity,
--   $$
--   m(t) \to \beta \qquad\text{and}\qquad M(t) \to \alpha\beta .
--   $$
--
--   Since an adaptive off-line adversary forces ratio $M(t)$ against every algorithm in the mates game, this limit is what lets the construction approach the upper bound $\alpha\beta$ of Theorem 2.2.
--
--   **Formalization Note.** $m$ and $M$ are the closed forms as sequences indexed by $t \in \mathbb N$; their values at $t = 0, 1$ do not affect the limits.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 12, §2, first paragraph ("as t tends to infinity, m tends to β and M tends to αβ")

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

open Filter Topology

/-- Manuscript p. 12, first paragraph: as `t → ∞`, `m(t) → β` and `M(t) → αβ`. -/
theorem params_tendsto (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (paramSmall α β) atTop (𝓝 β) ∧
      Tendsto (paramLarge α β) atTop (𝓝 (α * β)) := by sorry

end OnlineRandomization.Tightness
