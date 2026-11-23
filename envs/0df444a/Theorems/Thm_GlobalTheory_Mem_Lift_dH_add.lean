-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_dH_add
-- name    : GlobalTheory.Mem.Lift.dH_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:02.667792+00:00
-- url     : https://prove2.me/theorems/b3f8bebf-10fa-4254-9e6f-b49218a6eb06
-- title:
--   Lift: d H add
-- statement:
--   The Lift construction uses the d H add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfPlane.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfPlane.lean#L45-L56

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

theorem GlobalTheory.Mem.Lift.dH_add {ρ : V → B →L[ℂ] B} (v : V) {f g : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) (hg : _root_.GlobalTheory.RealWeil.Sm ρ g) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (f + g) =
      _root_.GlobalTheory.Mem.Lift.dH ρ v f + _root_.GlobalTheory.Mem.Lift.dH ρ v g := by sorry
