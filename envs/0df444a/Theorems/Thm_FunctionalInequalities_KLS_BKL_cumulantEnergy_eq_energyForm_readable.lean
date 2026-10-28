-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_cumulantEnergy_eq_energyForm_readable
-- name    : FunctionalInequalities.KLS.BKL.cumulantEnergy_eq_energyForm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:53.677238+00:00
-- url     : https://prove2.me/theorems/cc66c747-176c-41c7-bc23-026b31c6b211
-- title:
--   Cumulant Energy in Conjugated Coordinates
-- statement:
--   This statement expresses cumulant energy as a coordinate energy form, corresponding to the conjugation identities (83) and (85) of the Bizeul–Klartag–Lehec framework.
--
--   Let $\nu$ be a measure on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$ whose covariance operator $A$ is positive and invertible. Let $P$ be a self-adjoint invertible continuous linear map. For every $r\in\mathbb{N}$ and $u$, one has
--
--   $$
--   \operatorname{cumulantEnergy}(\nu,r,u)
--   =
--   \operatorname{energyForm}\!\left(PAP,\;K\mapsto
--   \kappa_{r+1}\bigl(\nu;u,Pe_{K_1},\ldots,Pe_{K_r}\bigr)\right).
--   $$
--
--   Here $e_j$ is the standard basis and `energyForm` is the coordinate-tensor quadratic form. The identity is a finite-dimensional change-of-coordinates formula for cumulant energies.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulantEnergy_eq_energyForm (ν : Measure (EuclideanSpace ℝ (Fin n)))
--       (hpos : (Covariance.operator ν).IsPositive) (hunit : IsUnit (Covariance.operator ν))
--       (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hP : IsSelfAdjoint P) (hPu : IsUnit P)
--       (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
--       cumulantEnergy ν r u =
--         energyForm (P * Covariance.operator ν * P)
--           (fun K : Fin r → Fin n => cumulant ν (r + 1) (Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s))))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnergy/Conjugation`](https://prove2.me/theorems/44ac1865-c5a7-46f3-bb27-cb9b8ec7e3f5).
--
--   Definition modules: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   [Source excerpt, lines 105–111](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Conjugation.lean#L105-L111) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Conjugation.lean#L102-L164 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Conjugation`, declaration `FunctionalInequalities.KLS.BKL.cumulantEnergy_eq_energyForm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Conjugation

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.CoordinateTensor
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.cumulantEnergy_eq_energyForm_readable (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hpos : (Covariance.operator ν).IsPositive) (hunit : IsUnit (Covariance.operator ν))
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hP : IsSelfAdjoint P) (hPu : IsUnit P)
    (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy ν r u =
      energyForm (P * Covariance.operator ν * P)
        (fun K : Fin r → Fin n => cumulant ν (r + 1) (Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s)))) := by sorry
