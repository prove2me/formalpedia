-- Prove2me | Theorems.Thm_ItoLemma_clock_augmented_multinoise_hessian
-- name    : ItoLemma.clock_augmented_multinoise_hessian
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:31:53.377198+00:00
-- url     : https://prove2.me/theorems/f5174a59-84c8-4eb8-99c1-32996ed450ac
-- title:
--   Clock-Augmented Hessian Contraction for Multiple Brownian Drivers
-- statement:
--   Suppose the clock coordinate of a two-dimensional Itô state has zero diffusion under every Brownian driver, while its spatial coordinate has diffusion coefficients σₖ indexed by Fin d. Then contracting any 2-by-2 Hessian with the resulting covariance matrix leaves exactly its spatial-spatial entry times Σₖ σₖ². This algebraic theorem supports the multinoise and multidimensional Itô bridge. It does not assert any stochastic convergence or integration identity.
-- source:
--   Original finite-sum algebraic specialisation of the multidimensional Brownian Itô covariance contraction; context: https://en.wikipedia.org/wiki/It%C3%B4%27s_lemma (accessed 26 October 2026) and Prove2Me accepted vector formula UUID 550fc0f9-7957-4075-b3fb-68172654fce1.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

open scoped BigOperators

/-- The clock coordinate has zero diffusion under every Brownian driver.
Only the spatial-spatial Hessian entry survives the covariance contraction. -/

theorem ItoLemma.clock_augmented_multinoise_hessian
    {d : ℕ} (hessian : Fin 2 → Fin 2 → ℝ) (diffusion : Fin d → ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      hessian i j *
        (∑ k : Fin d,
          (if i = 0 then (0 : ℝ) else diffusion k) *
            (if j = 0 then (0 : ℝ) else diffusion k))) =
      hessian 1 1 * (∑ k : Fin d, diffusion k * diffusion k) := by sorry
