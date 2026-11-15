-- Prove2me | Theorems.Thm_Kyprianou_Ch01_strictStableTimeScaling
-- name    : Kyprianou.Ch01.strictStableTimeScaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:12:09.530356+00:00
-- url     : https://prove2.me/theorems/3bf8c4b3-f788-41a6-b03e-9a89c23ce9c1
-- title:
--   §1.2.6: self-similarity of strictly stable Lévy processes
-- statement:
--   A strictly α-stable Lévy process has homogeneous exponent Ψ(cθ)=c^αΨ(θ), and consequently X_(scale·t) is distributed like scale^(1/α) X_t for every positive scale. Uses actual probability-law equality, not an arbitrary assigned distribution. This remains an uncompiled draft theorem.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.6, pp. 10–11.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.strictStableTimeScaling
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (alpha : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (hX : IsLevyProcess X P)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (Psi : ℝ → ℂ)
    (hchar : ∀ (t : ℝ≥0) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (-((t : ℝ) : ℂ) * Psi xi))
    (hhomog : ∀ c : ℝ, 0 < c → ∀ xi : ℝ,
      Psi (c * xi) = ((c ^ alpha : ℝ) : ℂ) * Psi xi) :
    ∀ (scale t : ℝ≥0), 0 < scale →
      P.map (X (scale * t)) =
        P.map (fun ω => (scale : ℝ) ^ (1 / alpha) * X t ω) := by
  sorry
