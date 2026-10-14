-- Prove2me | Theorems.Thm_Multihoming_Thresholds_ePi_sub_eP
-- name    : Multihoming.Thresholds.ePi_sub_eP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:37.422602+00:00
-- url     : https://prove2.me/theorems/a2a31b63-f635-433d-bd92-8d2f1f01f22b
-- title:
--   Appendix A1, PDF pp. 27–28 (printed pp. 21–22) — e_π − e_p = 2(2t − μ)(t√(t² − μ²) − (t − μ)²)/(4t² − 3tμ + μ²)
-- statement:
--   Let $t>0$ and $0\le\mu<t$, with $e_p=2(t-\mu)$ the price threshold and $e_\pi$ the profit threshold of Appendix A1. Then
--   $$e_\pi-e_p=2(2t-\mu)\,\frac{t\sqrt{t^2-\mu^2}-(t-\mu)^2}{4t^2-3t\mu+\mu^2}.$$
--
--   This identity reduces the comparison $e_p<e_\pi$ to the sign of $t\sqrt{t^2-\mu^2}-(t-\mu)^2$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, display "e_π − e_p = …" (introduced at the foot of PDF p. 27)

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem ePi_sub_eP (t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    ePi t μ - eP t μ =
      2 * (2 * t - μ) * (t * Real.sqrt (t ^ 2 - μ ^ 2) - (t - μ) ^ 2) /
        (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by sorry

end Multihoming.Thresholds
