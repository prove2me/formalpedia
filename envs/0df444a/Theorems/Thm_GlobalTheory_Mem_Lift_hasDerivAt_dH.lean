-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_hasDerivAt_dH
-- name    : GlobalTheory.Mem.Lift.hasDerivAt_dH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:46.612649+00:00
-- url     : https://prove2.me/theorems/3760d6ce-1172-4fd9-910d-0d8cdcc4bff5
-- title:
--   Lift: has Deriv At d H
-- statement:
--   The Lift construction uses the has Deriv At d H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfPlane.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfPlane.lean#L77-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped ContDiff Real
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
open MeasureTheory Complex Matrix
open scoped ContDiff Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B]

theorem GlobalTheory.Mem.Lift.hasDerivAt_dH {ρ : V → B →L[ℂ] B} (v : V) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (_root_.GlobalTheory.Mem.Lift.dH ρ v f) 0 := by sorry
