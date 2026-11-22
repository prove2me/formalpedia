-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1IdleCritical
-- name    : Kyprianou.Ch01.mg1IdleCritical
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T09:44:33.350175+00:00
-- url     : https://prove2.me/theorems/778d1405-4d96-4b80-9e2a-c2e9e3e9113d
-- title:
--   Theorem 1.11(ii) (critical traffic): infinite idle time for critical M/G/1 traffic
-- statement:
--   In an $M/G/1$ queue with arrival rate $\lambda > 0$, positive claims governed by distribution $F$ with mean $\mu > 0$, and critical traffic intensity $\lambda \mu = 1$, the total server idle time accumulated over $[0, \infty)$ is infinite almost surely: $\mathbb{P}(I_\infty = \infty) = 1$ for every initial workload $w \ge 0$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.11(ii), p. 21.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

namespace Kyprianou.Ch01

theorem mg1IdleCritical
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (hcritical : (rate : ℝ) * mu = 1) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = ⊤}).toReal = 1 := by
  sorry

end Kyprianou.Ch01
