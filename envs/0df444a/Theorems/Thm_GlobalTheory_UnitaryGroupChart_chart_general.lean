-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryGroupChart_chart_general
-- name    : GlobalTheory.UnitaryGroupChart.chart_general
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:24.327901+00:00
-- url     : https://prove2.me/theorems/8caf9084-71b4-4265-89a8-a827381696d1
-- title:
--   Unitary Group Chart: chart general
-- statement:
--   The Unitary Group Chart construction uses the chart general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianUnitaryGroupOneParameterChart.lean#L13-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianUnitaryGroupOneParameterChart.lean#L13-L98

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

theorem GlobalTheory.UnitaryGroupChart.chart_general {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1)
    {d e : ℕ} (Z : Fin d → E) (j : Fin e → Fin d) (hZσ : ∀ a, σ (Z a) = -Z a)
    (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : E → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : E), σ g * g = 1 →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by sorry
