-- Prove2me | Theorems.Thm_NoHair_kerrNewman_isStationaryBlackHole
-- name    : NoHair.kerrNewman_isStationaryBlackHole
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T21:59:41.725304+00:00
-- url     : https://prove2.me/theorems/d4aa60f2-99c7-4a52-9c28-6ba24b2ddbac
-- title:
--   Kerr–Newman spacetime satisfies the standing hypotheses
-- statement:
--   Let $m>0$ and $a^2+e^2\le m^2$. On the Kerr–Newman spacetime $\{r>0\}\subseteq\mathbb R^4$ with metric $g^{KN}_{m,a,e}$ and field $F^{KN}_{a,e}$ there exist a time orientation $T$, a symmetry flow $\varphi$ and a stationary asymptotically flat end $E$ such that all standing hypotheses of the mission hold (Lorentzian smooth metric, smooth 2-form, Einstein–Maxwell, stationarity, globally hyperbolic domain of outer communications, nonempty black-hole region, connected future event horizon), and the domain of outer communications is exactly $\{r>r_+\}$, $r_+=m+\sqrt{m^2-a^2-e^2}$.
--
--   This shows the hypotheses of the goal theorem are satisfiable and that the Kerr–Newman black holes themselves fall under the goal, so the goal is neither vacuous nor contradicted by its own model family.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone: Kerr–Newman is a stationary black hole.** For admissible parameters, the
Kerr–Newman spacetime `{r > 0}` satisfies all the standing hypotheses, and its domain of outer
communications is `{r > r₊}`. -/
theorem kerrNewman_isStationaryBlackHole (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ∃ (T : VecField (kerrNewmanSpacetime a))
      (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
      (E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ),
      IsStationaryBlackHole (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) T φ E ∧
      Subtype.val '' domainOfOuterCommunications (kerrNewmanMetricField m a e) T E.region
        = kerrNewmanDOC m a e := by
  sorry

end NoHair
