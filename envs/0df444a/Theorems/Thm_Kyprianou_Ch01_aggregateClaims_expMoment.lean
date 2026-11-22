-- Prove2me | Theorems.Thm_Kyprianou_Ch01_aggregateClaims_expMoment
-- name    : Kyprianou.Ch01.aggregateClaims_expMoment
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T09:21:38.278861+00:00
-- url     : https://prove2.me/theorems/c807cbd1-ae69-44cb-a271-46e61bad3a76
-- title:
--   Exponential moment of compound Poisson aggregate claims
-- statement:
--   Let $S_t=\sum_{i=0}^{N_t-1} Y_i$ be the aggregate claims process built from a compound Poisson driver: $N_t$ counts the arrivals of a Poisson process of rate $\lambda>0$ (i.i.d. exponential interarrival times) and the claims $(Y_i)$ are i.i.d. with law $F$, independent of the arrivals. Fix $\theta\in\mathbb R$ and a time $t>0$, and suppose $e^{\theta S_t}$ is integrable. Then:
--
--   1. the claim law has a finite exponential moment, $\int e^{\theta y}\,F(dy)<\infty$;
--   2. the exponential moment of $S_t$ is given by
--   $$\mathbb E\big[e^{\theta S_t}\big] = \exp\Big(\lambda t\Big(\int_{\mathbb R} e^{\theta y}\,F(dy) - 1\Big)\Big).$$
--
--   This is the real-exponential (moment generating function) counterpart of the compound Poisson characteristic exponent. In the Cramér–Lundberg model it turns the Lundberg equation $\mathbb E\,e^{-\nu X_1}=1$ for the surplus $X_t = ct - S_t$ into the explicit equation $\lambda\big(\int e^{\nu y}F(dy) - 1\big) = c\nu$.
--
--   **Formalization Note.** `aggregateClaims arrival claims t` is the driftless compound Poisson path at time $t$, i.e. $S_t$; the binder `arrival` is the interarrival sequence of the driver.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, §1.2.2 (compound Poisson process) together with Theorem 3.6 (exponential moments, $\mathbb E e^{\beta X_t} = e^{-t\Psi(-i\beta)}$); used in §1.3.1 for the Cramér–Lundberg Laplace exponent.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.aggregateClaims_expMoment
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (θ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hint : Integrable
      (fun ω => Real.exp (θ * aggregateClaims arrival claims t ω)) P) :
    Integrable (fun y : ℝ => Real.exp (θ * y)) F ∧
      (∫ ω, Real.exp (θ * aggregateClaims arrival claims t ω) ∂P) =
        Real.exp ((rate : ℝ) * (t : ℝ) * ((∫ y, Real.exp (θ * y) ∂F) - 1)) := by
  sorry
