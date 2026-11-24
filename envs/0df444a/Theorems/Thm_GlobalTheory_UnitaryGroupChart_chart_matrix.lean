-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryGroupChart_chart_matrix
-- name    : GlobalTheory.UnitaryGroupChart.chart_matrix
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:19.626425+00:00
-- url     : https://prove2.me/theorems/c6f2d955-6b9e-4cd1-8a08-b978323cc3a9
-- title:
--   Unitary Group Chart: chart matrix
-- statement:
--   The Unitary Group Chart construction uses the chart matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianUnitaryGroupOneParameterChart.lean#L103-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianUnitaryGroupOneParameterChart.lean#L103-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianUnitaryGroupOneParameterChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitaryGroupChart
open Filter
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem GlobalTheory.UnitaryGroupChart.chart_matrix (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hdet : IsUnit H.det)
    (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d)
    (hZ : ∀ a, (Z a)ᴴ * H + H * Z a = 0) (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 →
      X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), gᴴ * H * g = H →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by sorry
