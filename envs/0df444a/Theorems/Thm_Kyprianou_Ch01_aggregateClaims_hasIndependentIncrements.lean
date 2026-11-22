-- Prove2me | Theorems.Thm_Kyprianou_Ch01_aggregateClaims_hasIndependentIncrements
-- name    : Kyprianou.Ch01.aggregateClaims_hasIndependentIncrements
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T10:25:18.396021+00:00
-- url     : https://prove2.me/theorems/fe0258ca-726e-4b02-9eea-af046630bdac
-- title:
--   Compound Poisson aggregate claims have independent increments
-- statement:
--   Let $(\tau_i)_{i\ge0}$ be i.i.d. exponential interarrival times of rate $\lambda>0$ and $(Y_i)_{i\ge0}$ i.i.d. marks with law $F$, all jointly independent (a compound Poisson driver). Let $N_t$ be the number of arrival times $T_n=\tau_0+\dots+\tau_n$ in $[0,t]$, and let
--   $$S_t=\sum_{i<N_t}Y_i,\qquad t\ge0,$$
--   be the aggregate claims (driftless compound Poisson) process. Then $S$ has independent increments: for every finite monotone grid $0\le t_0\le t_1\le\dots\le t_n$, the increments
--   $$S_{t_1}-S_{t_0},\ S_{t_2}-S_{t_1},\ \dots,\ S_{t_n}-S_{t_{n-1}}$$
--   are mutually independent.
--
--   This is the independent-increment half of the statement that the compound Poisson process is a Lévy process. It holds for the concrete path built from an arbitrary rate and mark law on an arbitrary probability space. Combined with a deterministic drift, it gives the Markov and martingale properties of the Cramér–Lundberg and M/G/1 processes.
--
--   **Formalization Note.** $S$ is `aggregateClaims arrival claims`, with `arrival` the interarrival sequence of `IsCompoundPoissonDriver`. Independence is `HasIndependentIncrements` from LeanLevy, stated for the raw paths; no almost-sure modification is used.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, §1.2.2 (the compound Poisson process is a Lévy process: independent increments).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.aggregateClaims_hasIndependentIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P) :
    HasIndependentIncrements (fun t : ℝ≥0 => aggregateClaims arrival claims t) P := by
  sorry
