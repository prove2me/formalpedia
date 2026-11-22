-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1StationaryWorkload_zero
-- name    : Kyprianou.Ch01.mg1StationaryWorkload_zero
-- status  : Open
-- author  : @coqelz
-- created : 2026-11-21T09:00:38.644939+00:00
-- url     : https://prove2.me/theorems/7565305d-c991-4f28-9b66-883c57cf88f3
-- title:
--   Theorem 1.12(i) (zero backlog): stationary M/G/1 workload Pollaczek–Khintchine limit
-- statement:
--   This is the zero-backlog stationary workload convergence of Theorem 1.12(i) from Kyprianou (2006).
--
--   Consider an M/G/1 queue driven by a compound Poisson arrival process with rate $\lambda > 0$ and service time distribution $ having finite positive mean $\mu = \int_0^\infty x \, dF(x) > 0$. In the subcritical traffic regime $\rho = \lambda \mu < 1$, let $\eta$ be the integrated tail probability measure satisfying $\eta([0, x]) = \frac{1}{\mu} \int_0^x (1 - F(y)) \, dy$.
--
--   Starting from an initially empty system ( = 0$), the cumulative distribution function of the workload process (0)$ converges weakly as  \to \infty$ to the Pollaczek--Khintchine distribution:
--
--   62059
--   \lim_{t \to \infty} P(W_t(0) \le x) = (1 - \rho) \sum_{k=0}^\infty \rho^k \eta^{*k}([0, x]) = \mathrm{pkCDF}(\eta, \rho, x)
--   62059
--
--   for all  \ge 0$.
--
--   Mathematically, by the duality lemma for Lévy processes, the workload (0) = \sup_{0 \le s \le t} (X_s - X_t)$ has the same law as the running maximum $\overline{Y}_t = \sup_{0 \le s \le t} (\sum_{i=1}^{N_s} \xi_i - s)$. As  \to \infty$, $\overline{Y}_t \uparrow \overline{Y}_\infty$ almost surely, where $\overline{Y}_\infty$ is the all-time maximum whose law is given by the Pollaczek--Khintchine formula.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.12(i), pp. 21–22.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1StationaryWorkload_zero
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
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (eta (Set.Iic x)).toReal = integratedTailCDF F mu x) :
    ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun t : ℝ≥0 =>
        (P {ω | queueWorkload arrival claims 0 t ω ≤ x}).toReal)
        atTop (nhds (pkCDF eta ((rate : ℝ) * mu) x)) := by
  sorry
