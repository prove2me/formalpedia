-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_dH_smul_left
-- name    : GlobalTheory.Mem.Lift.dH_smul_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:48.566075+00:00
-- url     : https://prove2.me/theorems/e0cffe4d-936b-59ac-a272-b8a8ec26c920
-- title:
--   Lift: d H smul left
-- statement:
--   The Lift construction uses the d H smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfPlane.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfPlane.lean#L37-L39

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

theorem GlobalTheory.Mem.Lift.dH_smul_left (ρ : V → B →L[ℂ] B) (r : ℝ) (v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (r • v) f = r • _root_.GlobalTheory.Mem.Lift.dH ρ v f := by sorry
