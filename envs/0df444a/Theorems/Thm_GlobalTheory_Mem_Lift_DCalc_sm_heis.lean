-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_sm_heis
-- name    : GlobalTheory.Mem.Lift.DCalc.sm_heis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:54.94358+00:00
-- url     : https://prove2.me/theorems/57194944-9554-4235-9d46-226506bb6cee
-- title:
--   DCalc: sm heis
-- statement:
--   The DCalc construction uses the sm heis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L55-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.DCalc
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}

theorem GlobalTheory.Mem.Lift.DCalc.sm_heis (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w : V) : Sm ρ (ρ w f) := by sorry
