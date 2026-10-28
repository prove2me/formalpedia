-- Prove2me | Theorems.Thm_OAI_CriticalSK_sphereTilted_smallBall_s2
-- name    : OAI.CriticalSK.sphereTilted_smallBall_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:51:39.395028+00:00
-- url     : https://prove2.me/theorems/3cd5330b-60a7-42b2-9dd0-de26d47d31bc
-- title:
--   OAI.CriticalSK.sphereTilted_smallBall_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.sphereTilted_smallBall` of [lean/OAI/MathematicalPhysics/CriticalSK/SphereSaddle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/SphereSaddle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise`, `open Set Metric MeasureTheory MeasureTheory.Measure`, `open scoped ENNReal NNReal Topology`, `open MeasureTheory MeasureTheory.Measure Set Metric`, `open scoped BigOperators ENNReal Topology`, `open Set MeasureTheory`, `open scoped BigOperators ENNReal`, `open MeasureTheory`, `open Finset Real`, `open Finset Real Filter`, `open scoped Topology`, `open MeasureTheory Filter Set Real`, `open scoped ENNReal NNReal BigOperators`, `open scoped NNReal ENNReal BigOperators`, `open scoped NNReal ENNReal`, `open ProbabilityTheory`):
--
--   ```lean
--   lemma sphereTilted_smallBall_s2 (lam : Fin (n+3) → ℝ) (a z : ℝ)
--       (v : Fin (n+3) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
--       (hq : ∀ i, (v i : ℝ)⁻¹ = z-a*lam i)
--       {s m d b : ℝ} (hs : 0 < s) (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1)
--       (hd : 0 < d) (hb : 0 ≤ b)
--       (hmean : (∑ i : Fin (n+1), (v i.succ.succ : ℝ)) = s-d)
--       (hvar : 128 * (∑ i : Fin (n+1), (v i.succ.succ : ℝ)^2) ≤ d^2) :
--       (sphereTilted lam a (Real.sqrt s)
--         {u : unitSphere (Fin (n+3)) | |u.val (0 : Fin (n+1)).succ.succ| ≤ b}).toReal ≤
--         4 * (b * Real.sqrt s) * (Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹ *
--           Real.exp (d/m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.sphereTilted` and `OAI.CriticalSK.unitSphere` (definitions bundle `OAIQ074C000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.spectralGood_natural_sphere_bounds_s2` of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/SphereSaddle.lean (declaration OAI.CriticalSK.sphereTilted_smallBall)

import Mathlib
import Definitions.Def_OAIQ074C000

section

attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
namespace CriticalSK

section

variable {n : ℕ}

lemma sphereTilted_smallBall_s2 (lam : Fin (n+3) → ℝ) (a z : ℝ)
    (v : Fin (n+3) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (hq : ∀ i, (v i : ℝ)⁻¹ = z-a*lam i)
    {s m d b : ℝ} (hs : 0 < s) (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1)
    (hd : 0 < d) (hb : 0 ≤ b)
    (hmean : (∑ i : Fin (n+1), (v i.succ.succ : ℝ)) = s-d)
    (hvar : 128 * (∑ i : Fin (n+1), (v i.succ.succ : ℝ)^2) ≤ d^2) :
    (sphereTilted lam a (Real.sqrt s)
      {u : unitSphere (Fin (n+3)) | |u.val (0 : Fin (n+1)).succ.succ| ≤ b}).toReal ≤
      4 * (b * Real.sqrt s) * (Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹ *
        Real.exp (d/m) := by
  sorry

end

end CriticalSK

end

end OAI
end
