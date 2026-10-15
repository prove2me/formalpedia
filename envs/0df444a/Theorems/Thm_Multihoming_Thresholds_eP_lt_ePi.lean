-- Prove2me | Theorems.Thm_Multihoming_Thresholds_eP_lt_ePi
-- name    : Multihoming.Thresholds.eP_lt_ePi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:43.733766+00:00
-- url     : https://prove2.me/theorems/2a7427fb-105b-4d8f-852f-481f9a97fbaa
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — the profit threshold exceeds the price threshold: e_π > e_p
-- statement:
--   Let $t>0$ and $0<\mu<t$. Then
--
--   1. $t\sqrt{t^2-\mu^2}>(t-\mu)^2$ holds if and only if $\mu(t-\mu)(4t^2-3t\mu+\mu^2)>0$;
--   2. the profit threshold exceeds the price threshold: $e_p<e_\pi$, where $e_p=2(t-\mu)$.
--
--   Item 2 is the clause "where $e_\pi>e_p$" of Proposition 2: there is a range $(e_p,e_\pi)$ of exclusive features in which network effects lower the price but still raise the profit.
--
--   **Formalization Note** Under the stated hypotheses both sides of item 1 are true; item 1 records the paper's equivalence step. The network effect is strict, $\mu>0$: at $\mu=0$, $e_\pi=e_p=2t$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, sentence after the e_π − e_p display

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem eP_lt_ePi (t μ : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    (t * Real.sqrt (t ^ 2 - μ ^ 2) > (t - μ) ^ 2 ↔
      μ * (t - μ) * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) > 0) ∧
    eP t μ < ePi t μ := by sorry

end Multihoming.Thresholds
