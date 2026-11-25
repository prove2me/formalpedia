-- Prove2me | Theorems.Thm_GlobalTheory_WeilSmooth_jx_mem_induced
-- name    : GlobalTheory.WeilSmooth.jx_mem_induced
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:48.620728+00:00
-- url     : https://prove2.me/theorems/e03388ee-42eb-4892-9343-7fd0245eb46d
-- title:
--   Weil Smooth: jx mem induced
-- statement:
--   The Weil Smooth construction uses the jx mem induced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L96-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L96-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.WeilSmooth
open GlobalTheory.JR
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.WeilSmooth.jx_mem_induced : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by sorry
