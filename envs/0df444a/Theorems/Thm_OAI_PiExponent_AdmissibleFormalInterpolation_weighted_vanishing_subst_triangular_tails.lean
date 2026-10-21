-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_vanishing_subst_triangular_tails
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_triangular_tails
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:41:00.194179+00:00
-- url     : https://prove2.me/theorems/11196702-4e4b-495f-a465-205b575c66c7
-- title:
--   Triangular formal tail substitutions preserve weighted coefficient vanishing
-- statement:
--   For positive real variable weights, replacing each noninitial variable by itself plus a univariate tail starting at degree T_i preserves coefficient vanishing below every real weighted threshold, provided T_i times the initial-variable weight is at least that variable's weight. These hypotheses force positive cutoffs and make the formal substitution admissible. The statement includes the one-variable case and nonpositive thresholds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_triangular_tails
    {m : ℕ} (q : Fin (m + 1) → ℝ) (T : Fin m → ℕ)
    (R : Fin m → PowerSeries ℂ)
    (hq : ∀ i, 0 < q i)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (hR : ∀ (i : Fin m) (k : ℕ), k < T i → PowerSeries.coeff k (R i) = 0)
    (H : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m (R i))) F) = 0 := by sorry
