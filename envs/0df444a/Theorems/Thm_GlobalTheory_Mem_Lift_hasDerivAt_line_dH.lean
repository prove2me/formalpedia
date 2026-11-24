-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_hasDerivAt_line_dH
-- name    : GlobalTheory.Mem.Lift.hasDerivAt_line_dH
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:04.187632+00:00
-- url     : https://prove2.me/theorems/d7025235-ca2d-4639-ae78-9ca1f85964c8
-- title:
--   Lift: has Deriv At line d H
-- statement:
--   The Lift construction uses the has Deriv At line d H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HasDerivAtLineDH.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HasDerivAtLineDH.lean#L13-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HasDerivAtLineDH
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
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift

theorem GlobalTheory.Mem.Lift.hasDerivAt_line_dH {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (h : IsHeis (fun x y => om x y) ρ) (v : V) {f : B} (hf : Sm ρ f) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (ρ (s • v) (dH ρ v f)) s := by sorry
