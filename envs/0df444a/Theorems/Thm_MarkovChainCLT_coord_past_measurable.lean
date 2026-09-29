-- Prove2me | Theorems.Thm_MarkovChainCLT_coord_past_measurable
-- name    : MarkovChainCLT.coord_past_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:47:37.035051+00:00
-- url     : https://prove2.me/theorems/0a7ac2e1-d90a-45b2-a2fd-c97123a75bba
-- title:
--   Coordinates are past-measurable
-- statement:
--   Each coordinate is measurable with respect to its own past.
--
--   For any sequence $Y_0,Y_1,\dots$ and $k\ge 0$, $Y_k$ is measurable with respect to $\sigma(Y_0,\dots,Y_k)$, since its pullback is one term of the supremum. No measurability of $Y$ is needed.
--
--   **Formalization Note** `processSigma Y (Set.Iic k)` is the supremum of pullbacks.
-- source:
--   Lattice property of processSigma; cf. mixing sup arguments

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.coord_past_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (Y : ℕ → Ω → E) (k : ℕ) : Measurable[processSigma Y (Set.Iic k)] (Y k) := by sorry
