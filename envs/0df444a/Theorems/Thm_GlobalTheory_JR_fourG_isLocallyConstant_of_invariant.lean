-- Prove2me | Theorems.Thm_GlobalTheory_JR_fourG_isLocallyConstant_of_invariant
-- name    : GlobalTheory.JR.fourG_isLocallyConstant_of_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:02.328916+00:00
-- url     : https://prove2.me/theorems/30891a78-8e03-4ecb-b72e-4c78424cc466
-- title:
--   JR: four G is Locally Constant of invariant
-- statement:
--   The JR construction uses the four G is Locally Constant of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantPartialFourierGLBlock.lean#L23-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantPartialFourierGLBlock.lean#L23-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantPartialFourierGLBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
open Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.fourG_isLocallyConstant_of_invariant :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [_root_.GlobalTheory.JR.Unram F E] (r : ℕ) (M : _root_.GlobalTheory.JR.Meas r F E) (ψ : AddChar F ℂ),
      _root_.GlobalTheory.JR.IsStdChar ψ → ∀ f' : _root_.GlobalTheory.JR.Gl r F → ℂ, _root_.GlobalTheory.JR.IsTest f' →
      (∃ U ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F), ∀ Y : _root_.GlobalTheory.JR.Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
      IsLocallyConstant (_root_.GlobalTheory.JR.fourG M ψ f') := by sorry
