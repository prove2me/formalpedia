-- Prove2me | Theorems.Thm_FrechetPrefs_sharper_estimate
-- name    : FrechetPrefs.sharper_estimate
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:59.400542+00:00
-- url     : https://prove2.me/theorems/128aeaf7-05b1-41ef-bc1e-798bce76dd5f
-- title:
--   p.ec7 — the sharper estimate $g\le z-\frac1\theta u'(z)$
-- statement:
--   Let $u$ satisfy Assumption 1, $\theta>0$ and $0<g\le z$ with $\frac1\theta u'(g)+g=z$. Then
--   $$g\le z-\frac1\theta u'(z).$$
--
--   Applied with $g=F_\theta^{-1}(s)$ and $z=F_B^{-1}(s)$, this improves $F_\theta^{-1}\le F_B^{-1}$ by the first-order term of the expansion.
--
--   Differences from the source:
--   - generalization: "If u′ is a decreasing function" → no such hypothesis; reason: Assumption 1 implies it (`inada_consequences`), so the printed conclusion is recovered
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), p.ec7

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- The sharper estimate, p.ec7 of manuscript MS-DEC-19-01009-REV: if `g ≤ z` and
`(1/θ) u′(g) + g = z`, then `g ≤ z − (1/θ) u′(z)`, since `u′` is decreasing.

**Formalization Note.** The page's condition "u′ is a decreasing function" follows from Assumption 1
(`inada_consequences`), so it is not a hypothesis. -/
theorem sharper_estimate (u : ℝ → ℝ) (hu : IsInadaUtility u) (θ g z : ℝ) (hθ : 0 < θ)
    (hg : 0 < g) (hgz : g ≤ z) (heq : 1 / θ * deriv u g + g = z) :
    g ≤ z - 1 / θ * deriv u z := by sorry

end FrechetPrefs
