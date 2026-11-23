-- Prove2me | Theorems.Thm_GlobalTheory_WeilSmooth_fix_n
-- name    : GlobalTheory.WeilSmooth.fix_n
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:17.975138+00:00
-- url     : https://prove2.me/theorems/5e387286-cebc-4165-826d-d1e66576c781
-- title:
--   Weil Smooth: fix n
-- statement:
--   The Weil Smooth construction uses the fix n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L63-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L63-L80

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

theorem GlobalTheory.WeilSmooth.fix_n [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) (ω : A.K → ℂ)
    (μ : Measure A.L) (γ : ℂ) (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ)
    (hW : A.IsWeil ψ x ω μ γ W) (f : A.L → ℂ) (hf : IsTest f) :
    ∀ᶠ z in 𝓝 (0 : A.K), W (nS z) f = f := by sorry
