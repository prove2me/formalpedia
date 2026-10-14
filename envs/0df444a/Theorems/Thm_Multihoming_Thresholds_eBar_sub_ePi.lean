-- Prove2me | Theorems.Thm_Multihoming_Thresholds_eBar_sub_ePi
-- name    : Multihoming.Thresholds.eBar_sub_ePi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:42.452573+00:00
-- url     : https://prove2.me/theorems/9c89ccca-68b4-4a99-9441-b7b4719dd99a
-- title:
--   Appendix A1, PDF p. 27 (printed p. 21) — ē − e_π = (2t − μ)(μ³ − tμ² + 2t³ − 2t²√(t² − μ²))/(t(4t² − 3tμ + μ²))
-- statement:
--   Let $t>0$ and $0\le\mu<t$, with $\overline e=(2t^2-\mu^2)/t$ the upper end of the partial-multihoming range (24) and $e_\pi$ the profit threshold of Appendix A1. Then
--   $$\overline e-e_\pi=(2t-\mu)\,\frac{\mu^3-t\mu^2+2t^3-2t^2\sqrt{t^2-\mu^2}}{t\,(4t^2-3t\mu+\mu^2)}.$$
--
--   This identity reduces the comparison $e_\pi<\overline e$ to the sign of the numerator.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 27 (printed p. 21), Appendix A1, display "ē − e_π = …"

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem eBar_sub_ePi (t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    eBar t μ - ePi t μ =
      (2 * t - μ) * (μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3 - 2 * t ^ 2 * Real.sqrt (t ^ 2 - μ ^ 2)) /
        (t * (4 * t ^ 2 - 3 * t * μ + μ ^ 2)) := by sorry

end Multihoming.Thresholds
