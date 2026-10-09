-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_CIR_lemma_4_5
-- name    : NearlyUnstableHawkes.CIR.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:55.547982+00:00
-- url     : https://prove2.me/theorems/0d36486f-7414-48ee-b42c-8ab08afe560a
-- title:
--   Lemma 4.5 — L² convergence of the resolvent density
-- statement:
--   Let $\rho^T$ be the rescaled Hawkes resolvent density, and suppose $T(1-a_T)\to\lambda>0$ under Assumption 1. Set $\rho(x)=(\lambda/m)e^{-x\lambda/m}$ for $x\ge0$. Then
--
--   $$\int_0^\infty|\rho^T(x)-\rho(x)|^2\,dx\longrightarrow0.$$
--
--   This is the quantitative density convergence used to control the error kernel in the CIR limit.
--
--   **Formalization Note** The nonnegative squared integral is represented as an extended nonnegative integral; its convergence to zero expresses the same $L^2$ convergence and does not assign a default real value to a nonintegrable function.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 17, Lemma 4.5

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting

open MeasureTheory Filter Topology Set

namespace NearlyUnstableHawkes.CIR

/-- Lemma 4.5, p. 17: convergence in L² of the rescaled resolvent density. -/
theorem lemma_4_5 (T a : ℕ → ℝ) (φ φ' : ℝ → ℝ)
    (m lam : ℝ) (hTpos : ∀ n, 0 < T n)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 1))
    (hlam : 0 < lam)
    (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (hφ : Assumption1 φ φ' m) :
    Tendsto (fun n => ∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal ((rho (fun s => a n * φ s) (T n) x -
        lam / m * Real.exp (-(lam / m) * x)) ^ 2)) atTop (𝓝 0) := by sorry

end NearlyUnstableHawkes.CIR
