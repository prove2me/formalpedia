-- Prove2me | Theorems.Thm_Multihoming_Thresholds_eLow_lt_eP
-- name    : Multihoming.Thresholds.eLow_lt_eP
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:51.426528+00:00
-- url     : https://prove2.me/theorems/9aecd7f1-f760-4942-b897-ed16dab5f71c
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — e_p − e̲ = (t − μ)(2t − μ)/(2t) > 0
-- statement:
--   Let $t>0$ and $0\le\mu<t$, with $\underline e=(t-\mu)(2t+\mu)/(2t)$ the lower end of the partial-multihoming range (24) and $e_p=2(t-\mu)$. Then
--   $$e_p-\underline e=\frac{(t-\mu)(2t-\mu)}{2t}>0 .$$
--
--   So the price threshold lies strictly above the lower end of the partial-multihoming range.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, display "e_p − e̲ = …"

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem eLow_lt_eP (t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    eP t μ - eLow t μ = (t - μ) * (2 * t - μ) / (2 * t) ∧ eLow t μ < eP t μ := by sorry

end Multihoming.Thresholds
