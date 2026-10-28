-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_cumulantEnergy_succ_eq_readable
-- name    : FunctionalInequalities.KLS.BKL.cumulantEnergy_succ_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:29.396826+00:00
-- url     : https://prove2.me/theorems/a8033ec2-2b13-4f3a-8086-a0cc4a62b333
-- title:
--   Successor Cumulant Energy Reindexing
-- statement:
--   This is the reindexing identity for the next cumulant energy, corresponding to BKL equation (90).
--
--   Let $\nu$ be any measure on $\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$, let $r\in\mathbb N$, and let $u$ be a direction. Set $\sigma=\operatorname{Cov}(\nu)^{-1/2}$ using `inverseSqrt`. Then
--
--   $$
--   E_{r+1}^{\nu}(u)=\sum_{K:\,\mathrm{Fin}(r)\to\mathrm{Fin}(n)}\sum_{k:\,\mathrm{Fin}(n)}
--   \kappa_{r+2}^{\nu}\!\left(u,\sigma e_{K(0)},\ldots,\sigma e_{K(r-1)},\sigma e_k\right)^2.
--   $$
--
--   The finite sums are obtained by splitting the final index of a map from `Fin (r+1)` to `Fin n`. This is a combinatorial identity useful for comparing successive cumulant energies; no probability, isotropy, compactness, or invertibility assumptions are imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulantEnergy_succ_eq (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
--       cumulantEnergy ν (r + 1) u =
--         ∑ K : Fin r → Fin n, ∑ k : Fin n, cumulant ν (r + 1 + 1)
--           (Fin.cons u (Fin.snoc (fun s => inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
--             (inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ k)))) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/NoiseBound`](https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72).
--
--   Definition modules: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Previous: [`cumulant_middle_sum`](https://prove2.me/theorems/9e0a41d8-8c46-4618-8921-3e596dfd076a) · Next: [`sum_sq_conjugatedNoiseMatrix_mulVec_le`](https://prove2.me/theorems/bd7bc76e-3a86-4f3a-8622-a29d176bc214).
--
--   [Source excerpt, lines 99–103](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean#L99-L103) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean#L97-L180 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.NoiseBound`, declaration `FunctionalInequalities.KLS.BKL.cumulantEnergy_succ_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.cumulantEnergy_succ_eq_readable (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy ν (r + 1) u =
      ∑ K : Fin r → Fin n, ∑ k : Fin n, cumulant ν (r + 1 + 1)
        (Fin.cons u (Fin.snoc (fun s => inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
          (inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ k)))) ^ 2 := by sorry
