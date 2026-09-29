-- Prove2me | Theorems.Thm_KServer_race_gain_bound
-- name    : KServer.race_gain_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T19:32:49.345566+00:00
-- url     : https://prove2.me/theorems/78640e36-6325-4610-810f-6c06b4ee2374
-- title:
--   Anti-concentration gain of the coin race
-- statement:
--   The gain of the coin race. Consider the race of two level chunk systems $B_L, B_R$ (alongside head and closing systems) with $\kappa$ clamped coins, clamp $\varepsilon > 0$, sizes bounded by $c_B$, and both sides carrying a size window $c_{Lo}' \ge \varepsilon$ below all their chunk sizes. Then the expected imbalance of the consumed side masses satisfies
--   $$\sqrt{\frac{(\kappa\, c_{Lo}'^2)^3}{8 B^2 + 3\gamma^2 B}} - \kappa\varepsilon \;\le\; \mathbb{E}\,\lvert S_L - S_R \rvert,$$
--   where $B = \kappa\,(c_B+\varepsilon)^2$ and $\gamma = c_B + \varepsilon$. The imbalance is a bounded-increment martingale up to a drift of at most $\varepsilon$ per step (the clamped coin probabilities equalize the two conditional claims), with per-step conditional variance $n_L n_R \ge c_{Lo}'^2$ inside the window; the bound follows from the anti-concentration inequality for discrete martingales with pathwise variance windows. This gain term feeds the expected-total lower bound of the race: it is the mechanism by which the level step gains a $+\sqrt{\kappa}$-order term over the plain tripling, driving the $(\log k)^2$ recursion of the BCR lower bound.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_gain

namespace KServer

open Race

theorem race_gain_bound {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {cLo' : ℝ} (hεLo : ε ≤ cLo')
    (hLoL : ∀ (l : BL.Ω) (i : Fin BL.m), cLo' ≤ BL.size l i)
    (hLoR : ∀ (r : BR.Ω) (i : Fin BR.m), cLo' ≤ BR.size r i) :
    Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
      - (κ : ℝ) * ε
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| := by sorry

end KServer
