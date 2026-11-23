-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_heis_dH
-- name    : GlobalTheory.Mem.Lift.DCalc.heis_dH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:17.602249+00:00
-- url     : https://prove2.me/theorems/6d991c1f-91be-4259-9dd9-2d6eaaa8c5c4
-- title:
--   DCalc: heis d H
-- statement:
--   The DCalc construction uses the heis d H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L38-L53

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

theorem GlobalTheory.Mem.Lift.DCalc.heis_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w y : V) :
    ρ w (dH ρ y f) = fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f := by sorry
