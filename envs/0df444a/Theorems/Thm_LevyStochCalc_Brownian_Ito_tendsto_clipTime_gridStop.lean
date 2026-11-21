-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_clipTime_gridStop
-- name    : LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:14:57.785119+00:00
-- url     : https://prove2.me/theorems/2221afec-6f45-407e-b9c6-316798a3684e
-- title:
--   tendsto clipTime gridStop
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` is extracted from `LevyStochCalc.Ito.ItoFormulaStoppedLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a path stopped at an arbitrary stopping time

A stopping time is approximated from above by the stopping times that stop at the first point of
a uniform grid strictly beyond it, which take finitely many values. The horizons clipped at the
approximations converge to the horizon clipped at the stopping time, the integrands cut off at the
approximations converge in the energy of a window to the integrand cut off at the stopping time,
and Itô's formula along the finite-range stopped paths passes to the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` — the clipped horizons converge.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` — the cut-off integrands converge
  in the energy of the window.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` — the process stopped at a
  stopping time is the vector Itô process of the stopped coefficients.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section ClipLimit

variable {Ω : Type u}

theorem _root_.LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop (τ : Ω → WithTop ℝ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω) {t : ℝ} (ht : 0 < t) (ω : Ω) :
    Filter.Tendsto (fun m : ℕ => clipTime (gridStop τ t m) t ω) Filter.atTop
      (𝓝 (clipTime τ t ω)) := by sorry
