-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueUpperPassageProbability
-- name    : Kyprianou.Ch01.queueUpperPassageProbability
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T09:47:35.105491+00:00
-- url     : https://prove2.me/theorems/8da26763-f447-497b-b5e4-886bd596b369
-- title:
--   Exercise 1.9(ii): exact upward passage probability $\mathbb P(\sup_t X_t>x)=e^{-\theta^* x}$ for the overloaded M/G/1 surplus
-- statement:
--   Consider the M/G/1 / Cramér–Lundberg process with unit drift,
--   $$X_t = t - S_t,\qquad S_t=\sum_{i<N_t}Y_i,$$
--   built from a compound Poisson driver with arrival rate $\lambda>0$ and i.i.d. service times (claims) $Y_i\sim F$. Assume:
--
--   1. $F$ is concentrated on $(0,\infty)$, i.e. $F((-\infty,0])=0$;
--   2. $F$ has finite mean $\mu=\int z\,F(dz)$ and the queue is overloaded, $\lambda\mu>1$;
--   3. $\theta^*>0$ is a root of the Laplace exponent
--   $$\psi(\theta)=\theta-\lambda\int_{(0,\infty)}\big(1-e^{-\theta z}\big)\,F(dz),\qquad \psi(\theta^*)=0.$$
--
--   Then for every $x>0$,
--   $$\mathbb P\big(\exists\, t>0:\ X_t> x\big)=e^{-\theta^* x}.$$
--
--   Equivalently, the overall supremum $\sup_{t>0}X_t$ is exponentially distributed with parameter $\theta^*$. This is the second assertion of Kyprianou's Exercise 1.9(ii); together with the exponential martingale $e^{\theta^* X_t}$ (the first assertion) it describes the upward fluctuations of the overloaded M/G/1 surplus, which has no positive jumps and drifts to $-\infty$.
--
--   **Formalization Note.** $X$ is `riskSurplus arrival claims 1 0` and $\psi$ is `queueLaplaceExponent rate F`. The probability is the real value of the (outer) measure of the strict upward passage event.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 1, Exercise 1.9(ii), printed p. 31 (second assertion: the passage probability).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.queueUpperPassageProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPos : F (Set.Iic (0 : ℝ)) = 0)
    (hIntegrable : Integrable (fun z : ℝ => z) F)
    (mu : ℝ) (hMean : (∫ z, z ∂F) = mu)
    (hOverload : 1 < (rate : ℝ) * mu)
    (theta : ℝ) (hTheta : 0 < theta)
    (hRoot : queueLaplaceExponent rate F theta = 0) :
    ∀ x : ℝ, 0 < x →
      (P {ω | ∃ t : ℝ≥0, 0 < t ∧ x < riskSurplus arrival claims 1 0 t ω}).toReal =
        Real.exp (-theta * x) := by
  sorry
