-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1StationaryWorkload_coupling
-- name    : Kyprianou.Ch01.mg1StationaryWorkload_coupling
-- status  : Open
-- author  : @coqelz
-- created : 2026-11-21T09:00:40.326114+00:00
-- url     : https://prove2.me/theorems/e1a53bb6-6046-4732-a0b8-fc1da51197a7
-- title:
--   Theorem 1.12(i) (coupling): stationary M/G/1 workload limit invariance to initial backlog
-- statement:
--   This is the coupling invariance principle for the stationary M/G/1 workload distribution of Theorem 1.12(i) from Kyprianou (2006).
--
--   Consider an M/G/1 queue driven by a compound Poisson driver with arrival rate $\lambda > 0$, service distribution $, positive mean $\mu$, and subcritical traffic intensity $\rho = \lambda \mu < 1$.
--
--   Suppose that starting from an empty queue ( = 0$), the workload distribution converges weakly as  \to \infty$ to a limiting distribution function (x)$:
--
--   62059
--   \lim_{t \to \infty} P(W_t(0) \le x) = L(x) \quad \text{for all } x \ge 0.
--   62059
--
--   Then for any nonnegative initial backlog  \ge 0$, the workload distribution starting from $ converges to the exact same limit:
--
--   62059
--   \lim_{t \to \infty} P(W_t(w) \le x) = L(x) \quad \text{for all } x \ge 0.
--   62059
--
--   This decoupling property reflects the fact that under subcritical load ($\rho < 1$), the workload process reaches zero in finite time almost surely with finite expected busy period, so the influence of the initial backlog vanishes asymptotically.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.12(i), pp. 21–22.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1StationaryWorkload_coupling
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
    (hlight : (rate : ℝ) * mu < 1)
    (L : ℝ → ℝ)
    (hzero : ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun t : ℝ≥0 =>
        (P {ω | queueWorkload arrival claims 0 t ω ≤ x}).toReal)
        atTop (nhds (L x))) :
    ∀ w : ℝ, 0 ≤ w → ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun t : ℝ≥0 =>
        (P {ω | queueWorkload arrival claims w t ω ≤ x}).toReal)
        atTop (nhds (L x)) := by
  sorry
