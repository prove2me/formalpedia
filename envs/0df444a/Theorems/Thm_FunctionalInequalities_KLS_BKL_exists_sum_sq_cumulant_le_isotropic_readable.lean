-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_exists_sum_sq_cumulant_le_isotropic_readable
-- name    : FunctionalInequalities.KLS.BKL.exists_sum_sq_cumulant_le_isotropic_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:42.80998+00:00
-- url     : https://prove2.me/theorems/cfaadac6-0d48-4b92-9fe1-c1083e401bec
-- title:
--   Fixed-Dimension Cumulant Energy Bound
-- statement:
--   This statement gives a fixed-dimensional bound for the squared coordinate sum of a cumulant tensor.
--
--   For every $n,d\in\mathbb{N}$, there exists $b\ge0$ such that every compactly supported isotropic log-concave probability law $\nu$ on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$ and every $u$ satisfy
--
--   $$
--   \sum_{J:\operatorname{Fin}d\to\operatorname{Fin}n}
--   \kappa_{d+1}\bigl(\nu;u,e_{J_1},\ldots,e_{J_d}\bigr)^2
--   \le b\,\|u\|^2.
--   $$
--
--   The constant is allowed to depend on $n$ and $d$; this is an a-priori fixed-dimension estimate rather than a dimension-free theorem.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_sum_sq_cumulant_le_isotropic (d : ℕ) :
--       ∃ b : ℝ, 0 ≤ b ∧ ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
--         KLS.LogConcave ν → KLS.Isotropic ν → IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
--           ∀ u : EuclideanSpace ℝ (Fin n),
--             ∑ J : Fin d → Fin n, cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
--               (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnergy/Bound`](https://prove2.me/theorems/494b16b3-95d4-447e-8ef4-9ddd76f7af3b).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`exists_norm_cumulant_le_isotropic`](https://prove2.me/theorems/21946b44-1d94-42f6-9c1c-81a650d502c1).
--
--   Previous: [`exists_norm_cumulant_le_isotropic`](https://prove2.me/theorems/21946b44-1d94-42f6-9c1c-81a650d502c1).
--
--   [Source excerpt, lines 52–57](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Bound.lean#L52-L57) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Bound.lean#L51-L87 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Bound`, declaration `FunctionalInequalities.KLS.BKL.exists_sum_sq_cumulant_le_isotropic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Bound

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.exists_sum_sq_cumulant_le_isotropic_readable (d : ℕ) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      KLS.LogConcave ν → KLS.Isotropic ν → IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
        ∀ u : EuclideanSpace ℝ (Fin n),
          ∑ J : Fin d → Fin n, cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2 := by sorry
