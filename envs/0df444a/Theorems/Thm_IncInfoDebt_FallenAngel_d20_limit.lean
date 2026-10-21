-- Prove2me | Theorems.Thm_IncInfoDebt_FallenAngel_d20_limit
-- name    : IncInfoDebt.FallenAngel.d20_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:19.659813+00:00
-- url     : https://prove2.me/theorems/499a2877-f380-42e4-a30b-b8a29d1e44ef
-- title:
--   Equation (D.20) — default probability at a square-root distance from zero
-- statement:
--   Let $\sigma>0$, let $m$ be any real drift, and fix $\alpha>0$. A state at distance $\alpha\sigma\sqrt h$ from the default boundary has short-horizon no-default probability $S_h(\alpha\sigma\sqrt h)$. As $h$ decreases to zero,
--
--   $$1-S_h(\alpha\sigma\sqrt h)\longrightarrow 2N(-\alpha).$$
--
--   This is the boundary-scale probability in (D.20), used in the intensity calculation. The positive lag $L$ places the statement in Regime 4 but does not enter this short-horizon probability.
-- source:
--   Benzoni, Garlappi & Goldstein, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019), Online Appendix p. 17, proof of Corollary 1, (D.20), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

namespace IncInfoDebt.FallenAngel
open Filter

/-- Equation (D.20), Online Appendix p. 17: the boundary-scale default probability. -/
theorem d20_limit (σ m L α : ℝ) (hP : Standing σ L) (hα : 0 < α) :
    Tendsto (fun h : ℝ => 1 - survival σ m h (α * σ * Real.sqrt h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * N (-α))) := by sorry

end IncInfoDebt.FallenAngel
