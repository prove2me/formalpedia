-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lundbergRootEquation
-- name    : Kyprianou.Ch01.lundbergRootEquation
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T09:19:44.996089+00:00
-- url     : https://prove2.me/theorems/e30387c2-ab53-45e5-9ad9-8a71db3c99d1
-- title:
--   Cramér root of the surplus exponential moment gives the Lundberg equation
-- statement:
--   In the Cramér–Lundberg model the surplus from zero capital is $X_t=ct-S_t$, where $S_t=\sum_{i\le N_t}\xi_i$ is compound Poisson with rate $\lambda>0$ and claim law $F$ on $(0,\infty)$, and $c>0$ is the premium rate. Suppose $\nu>0$ is such that $e^{-\nu X_1}$ is integrable and
--
--   $$\mathbb E\big[e^{-\nu X_1}\big]=1 .$$
--
--   Then the claim law has a finite exponential moment of order $\nu$, i.e. $x\mapsto e^{\nu x}$ is $F$-integrable, and $\nu$ solves the Lundberg equation
--
--   $$\lambda\int_{(0,\infty)}\big(e^{\nu x}-1\big)\,F(dx)\;=\;c\,\nu .$$
--
--   The proof is the compound-Poisson moment formula $\mathbb E[e^{\nu S_1}]=\exp\big(\lambda(\hat F(\nu)-1)\big)$ (finite iff $\hat F(\nu)=\int e^{\nu x}F(dx)<\infty$), so that $\mathbb E[e^{-\nu X_1}]=\exp\big(-c\nu+\lambda(\hat F(\nu)-1)\big)$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, §1.3.1, Theorems 1.8–1.10, pp. 15–18 (the Cramér condition in Theorem 1.10, rewritten via the compound Poisson Laplace exponent)

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.lundbergRootEquation
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (premium : ℝ) (hpremium : 0 < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1) :
    Integrable (fun x : ℝ => Real.exp (nu * x)) F ∧
      (rate : ℝ) * (∫ x, (Real.exp (nu * x) - 1) ∂F) = premium * nu := by
  sorry
