-- Prove2me | Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_stationary
-- name    : Kyprianou.Ch01.riskSurplus_increment_stationary
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T10:07:08.318246+00:00
-- url     : https://prove2.me/theorems/19963a34-cc7a-401d-9503-66ea05550e2b
-- title:
--   Cramér–Lundberg surplus increments are stationary
-- statement:
--   Let $(\tau_i)_{i\ge 0}$ be i.i.d. exponential interarrival times with rate $\lambda > 0$ and $(Y_i)_{i\ge 0}$ i.i.d. claim sizes with distribution $F$, jointly independent on $(\Omega, \mathcal{F}, P)$. Let $X_t = c t - S_t$ be the Cramér–Lundberg surplus process starting at $0$ with premium rate $c$, where $S_t = \sum_{i < N_t} Y_i$ is the aggregate claim process. For any $0 \le s \le t$, the increment $X_t - X_s$ has identical law under $P$ to the surplus $X_{t - s}$ at lag $t - s$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, §1.2.2 and §1.3.1–1.3.2; used in Exercise 1.9(ii), p. 31.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch01

theorem riskSurplus_increment_stationary
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (premium : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    P.map (fun ω => riskSurplus arrival claims premium 0 t ω -
        riskSurplus arrival claims premium 0 s ω) =
      P.map (riskSurplus arrival claims premium 0 (t - s)) := by
  sorry

end Kyprianou.Ch01
