-- Prove2me | Theorems.Thm_Multihoming_Thresholds_ePi_lt_eBar
-- name    : Multihoming.Thresholds.ePi_lt_eBar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:42.228984+00:00
-- url     : https://prove2.me/theorems/f91e6333-457e-4bde-9f1f-be86dbfc6a49
-- title:
--   Appendix A1 and footnote 19, PDF p. 27 (printed p. 21) — the profit threshold lies below ē: e_π < ē
-- statement:
--   Let $t>0$ and $0<\mu<t$. Then
--
--   1. (footnote 19) the bracket is positive: $4t^2-3t\mu+\mu^2>0$;
--   2. the squared comparison reduces to a product:
--   $$\bigl(\mu^3-t\mu^2+2t^3\bigr)^2-4t^4\bigl(-\mu^2+t^2\bigr)=\mu^3(t+\mu)\bigl(4t^2-3t\mu+\mu^2\bigr);$$
--   3. the profit threshold lies strictly below the upper end of the partial-multihoming range: $e_\pi<\overline e$, where $\overline e=(2t^2-\mu^2)/t$.
--
--   Together with $e_p>\underline e$ this places both thresholds of Proposition 2 inside the partial-multihoming range.
--
--   **Formalization Note** Item 2 is the polynomial identity behind the paper's sentence "This holds if $\mu^3(t+\mu)(4t^2-3t\mu+\mu^2)>0$". The network effect is strict, $\mu>0$: at $\mu=0$, $e_\pi=\overline e=2t$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 27 (printed p. 21), Appendix A1, sentence after the ē − e_π display, and footnote 19

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem ePi_lt_eBar (t μ : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    0 < 4 * t ^ 2 - 3 * t * μ + μ ^ 2 ∧
    (μ ^ 3 - t * μ ^ 2 + 2 * t ^ 3) ^ 2 - 4 * t ^ 4 * (-μ ^ 2 + t ^ 2) =
      μ ^ 3 * (t + μ) * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) ∧
    ePi t μ < eBar t μ := by sorry

end Multihoming.Thresholds
