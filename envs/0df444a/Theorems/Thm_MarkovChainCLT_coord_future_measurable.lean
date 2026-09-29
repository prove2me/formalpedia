-- Prove2me | Theorems.Thm_MarkovChainCLT_coord_future_measurable
-- name    : MarkovChainCLT.coord_future_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:47:40.02964+00:00
-- url     : https://prove2.me/theorems/fcc023f1-86aa-4178-8daf-d5d1edc22bb7
-- title:
--   Coordinates are future-measurable
-- statement:
--   Each coordinate is measurable with respect to its own future.
--
--   For any sequence and $m\ge 0$, $Y_m$ is measurable with respect to $\sigma(Y_m,Y_{m+1},\dots)$.
--
--   **Formalization Note** As above with `Set.Ici`.
-- source:
--   Lattice property of processSigma

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.coord_future_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (Y : ℕ → Ω → E) (m : ℕ) : Measurable[processSigma Y (Set.Ici m)] (Y m) := by sorry
