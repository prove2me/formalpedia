-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_add_le
-- name    : LevyStochCalc.Ito.Picard.bieleckiNorm_add_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:22:22.253152+00:00
-- url     : https://prove2.me/theorems/b3547480-5d60-4427-afde-58a90d2debea
-- title:
--   bieleckiNorm add le
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_add_le` is extracted from `LevyStochCalc.Ito.PicardSpaceBieleckiEDist`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiEDist_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Bielecki β-weighted pseudo-edist between bounded processes

Pointwise Euclidean Minkowski on `Fin n → ℝ` lifts, through `L²`-Minkowski over `Ω`,
multiplication by the weight `exp (-β * t)` and sup-subadditivity over `t ∈ [0, T]`, to
subadditivity of the Bielecki β-norm `bieleckiNorm β T X = ⨆ t ∈ [0, T], exp (-β * t) *
(E‖X t‖²)^(1/2)`. Evaluating that norm on the pointwise path difference of two
`SBoundedProcess`es gives `bieleckiEDist`, which vanishes on the diagonal and is symmetric;
two processes whose paths agree P-a.s. at every `t` are at Bielecki distance zero, so it is a
pseudo-edist rather than an edist.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Pointwise Euclidean Minkowski on `Fin n → ℝ`

The Bielecki β-norm has the inner part `(∑ i, ‖X t ω i‖₊²)^(1/2)` which
is the **Euclidean** norm of `X t ω : Fin n → ℝ` (NOT the sup-norm `Pi.norm_def`
of Mathlib's default `Pi.seminormedAddGroup`). The triangle inequality
requires `(∑ i, (a_i + b_i)²)^(1/2) ≤ (∑ i, a_i²)^(1/2) + (∑ i, b_i²)^(1/2)`,
which is `NNReal.Lp_add_le` at `p = 2`. -/

/-! ### Bielecki edist between `SBoundedProcess`es

Defined as `bieleckiNorm β T (X.X - Y.X)`. The path map difference is
just pointwise subtraction. -/

/-! ### Pseudo-edist axioms for `bieleckiEDist` -/

/-! ### Bielecki triangle inequality

The key analytic content: `bieleckiNorm β T ((X - Y) + (Y - Z)) ≤
bieleckiNorm β T (X - Y) + bieleckiNorm β T (Y - Z)`.

This decomposes as:
1. Pointwise (in `t, ω`) Euclidean Minkowski (`sum_sq_nnreal_add_le`).
2. L² Minkowski over `ω` (`ENNReal.lintegral_Lp_add_le`).
3. Multiplication by `ENNReal.ofReal (Real.exp (-β·t))` preserves the
   inequality (left-multiplication by a non-negative constant in ℝ≥0∞).
4. Sup-subadditivity (`iSup₂_add_le`).
-/

theorem _root_.LevyStochCalc.Ito.Picard.bieleckiNorm_add_le
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (β T : ℝ)
    (Y₁ Y₂ : ℝ → Ω → (Fin n → ℝ))
    (hY₁_meas : ∀ t : ℝ, AEMeasurable
      (fun ω => (∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P)
    (hY₂_meas : ∀ t : ℝ, AEMeasurable
      (fun ω => (∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P) :
    bieleckiNorm (P := P) β T (fun t ω => Y₁ t ω + Y₂ t ω)
      ≤ bieleckiNorm (P := P) β T Y₁ + bieleckiNorm (P := P) β T Y₂ := by sorry
