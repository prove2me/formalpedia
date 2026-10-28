-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_exists_norm_cumulant_le_isotropic_readable
-- name    : FunctionalInequalities.KLS.BKL.exists_norm_cumulant_le_isotropic_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:36.204297+00:00
-- url     : https://prove2.me/theorems/21946b44-1d94-42f6-9c1c-81a650d502c1
-- title:
--   Fixed-Dimension Cumulant Norm Bound
-- statement:
--   This statement gives an a-priori cumulant bound in each fixed dimension.
--
--   For every $n,m\in\mathbb{N}$, there exists a constant $C\ge0$ such that every probability law $\nu$ on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$ that is log-concave, isotropic, and compactly supported satisfies
--
--   $$
--   \left\|\kappa_m(\nu)\right\|\le C.
--   $$
--
--   The constant may depend on both $n$ and $m$; the statement does not assert a universal or dimension-free bound. It provides fixed-dimensional control for later energy estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_norm_cumulant_le_isotropic (m : ℕ) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
--         KLS.LogConcave ν → KLS.Isotropic ν → IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
--           ‖cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m‖ ≤ C
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnergy/Bound`](https://prove2.me/theorems/494b16b3-95d4-447e-8ef4-9ddd76f7af3b).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`norm_cumulant_le_of_moment_bounds`](https://prove2.me/theorems/2fba5017-7028-4900-bbca-722c2b963872), [`Isotropic.integral_norm_sq`](https://prove2.me/theorems/d8804772-cf20-4fb4-8ca9-55643b773065).
--
--   Next: [`exists_sum_sq_cumulant_le_isotropic`](https://prove2.me/theorems/cfaadac6-0d48-4b92-9fe1-c1083e401bec).
--
--   [Source excerpt, lines 20–23](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Bound.lean#L20-L23) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Bound.lean#L19-L49 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Bound`, declaration `FunctionalInequalities.KLS.BKL.exists_norm_cumulant_le_isotropic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Bound

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.exists_norm_cumulant_le_isotropic_readable (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      KLS.LogConcave ν → KLS.Isotropic ν → IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
        ‖cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m‖ ≤ C := by sorry
