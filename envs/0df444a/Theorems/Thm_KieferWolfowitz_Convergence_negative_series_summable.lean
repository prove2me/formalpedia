-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_negative_series_summable
-- name    : KieferWolfowitz.Convergence.negative_series_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:48:34.177648+00:00
-- url     : https://prove2.me/theorems/e39d5e69-3137-4595-b398-dd67abe98ab1
-- title:
--   (3.15), p. 464 — the negative-term series $\sum (a_n/c_n)N_n$ converges
-- statement:
--   Assume the model of the paper: observation laws $H$ with regression function $M$ satisfying (2.2) with constant $S$; $M$ strictly increasing for $x<\theta$ and strictly decreasing for $x>\theta$; Conditions 1 and 2 (with some positive constants $\beta,B$ and $\rho,R$); step sizes satisfying (2.3)–(2.6); and a Kiefer–Wolfowitz process $(z_n,y_{2n-1},y_{2n})$. With $U_n^-(z)=\min\big(U_n(z),0\big)$ and $N_n=E\,U_n^-(z_n)$, every $U_n^-(z_n)$ is integrable and the series
--   $$\sum_{n=1}^{\infty}\frac{a_n}{c_n}\,N_n$$
--   converges.
--
--   The terms are nonpositive, so the claim is that the drift toward $\theta$, weighted by $a_n/c_n$, has finite total. Together with the convergence of $\sum(a_n/c_n)P_n$ and the divergence of $\sum a_n$ this forces $E\{K_n|z_n-\theta|\}$ to be small infinitely often (3.18).
--
--   **Formalization Note** Condition 3 is not needed and is omitted from the hypotheses (the step-size bundle still contains $\sum a_n=\infty$, which this step does not use). Integrability of $U_n^-(z_n)$ is part of the conclusion, so the series is not made of Lean's default values $0$. Lean index $n$ is the paper's $n+1$.
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), p. 464, (3.15)

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), (3.15), p. 464: the negative-term series `Σ (a_n/c_n) N_n`,
`N_n = E U_n⁻(z_n)`, converges (each `U_n⁻(z_n)` being integrable). -/
theorem negative_series_summable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (S θ : ℝ)
    (hS : SecondMomentBound H S) (hM : Unimodal (regFun H) θ)
    (h1 : ∃ β B : ℝ, 0 < β ∧ 0 < B ∧ Cond1 (regFun H) θ β B)
    (h2 : ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ Cond2 (regFun H) ρ R)
    (a c : ℕ → ℝ) (hac : StepSizes a c) (z₁ : ℝ)
    (z yminus yplus : ℕ → Ω → ℝ) (hz : IsKWProcess H a c z₁ P ℱ z yminus yplus) :
    (∀ n, Integrable (fun ω => Uminus (regFun H) θ (c n) (z n ω)) P) ∧
    Summable (fun n => a n / c n * ∫ ω, Uminus (regFun H) θ (c n) (z n ω) ∂P) := by sorry

end KieferWolfowitz.Convergence
