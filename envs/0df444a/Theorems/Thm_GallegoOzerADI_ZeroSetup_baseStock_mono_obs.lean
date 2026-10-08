-- Prove2me | Theorems.Thm_GallegoOzerADI_ZeroSetup_baseStock_mono_obs
-- name    : GallegoOzerADI.ZeroSetup.baseStock_mono_obs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:57:11.826399+00:00
-- url     : https://prove2.me/theorems/8c691053-4a3a-436d-9078-6cf06342affb
-- title:
--   Theorem 4, Part 5 — the base-stock level $y_t(o_t)$ is increasing in $o_t$
-- statement:
--   In the inventory model with advance demand information and zero set-up cost, under its standing hypotheses, fix a period $t \in \{1, \dots, T\}$. For a vector $o$ of observed demands beyond the protection period let $y_t(o)$ be the base-stock level of Eq. (11), the smallest minimizer of $V_t(\cdot, o)$. If $o \le o'$ componentwise, then
--
--   $$y_t(o) \le y_t(o').$$
--
--   Systems that observe more demand for periods beyond the protection period hold higher order-up-to levels.
--
--   **Formalization Note.** "Increasing" means nondecreasing (footnote 3, p. 1345). The levels are given as hypotheses characterising $y$ and $y'$ as smallest minimizers of $V_t(\cdot, o)$ and $V_t(\cdot, o')$; their existence is Theorem 4, Part 2.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Theorem 4, Part 5

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 5 (p. 1351): for every period `t ∈ {1, …, T}`, the base-stock level `y_t(o_t)`
(the smallest minimizer of `V_t(·, o_t)`, Eq. (11)) is increasing (nondecreasing) in `o_t` for the
componentwise order. -/
theorem baseStock_mono_obs {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o o' : Fin M → ℝ) (y y' : ℝ)
    (hoo : o ≤ o') (hy : IsLeastMinimizer (fun z => P.V t z o) y)
    (hy' : IsLeastMinimizer (fun z => P.V t z o') y') :
    y ≤ y' := by sorry

end GallegoOzerADI.ZeroSetup
