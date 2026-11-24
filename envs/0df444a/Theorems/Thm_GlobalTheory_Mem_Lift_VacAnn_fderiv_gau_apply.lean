-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_VacAnn_fderiv_gau_apply
-- name    : GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:38.36458+00:00
-- url     : https://prove2.me/theorems/df3d1207-1953-4cf7-8bf0-72d7e072f2cf
-- title:
--   Vac Ann: fderiv gau apply
-- statement:
--   The Vac Ann construction uses the fderiv gau apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VacuumProjectorRangeAnnihilated.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VacuumProjectorRangeAnnihilated.lean#L34-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VacuumProjectorRangeAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.VacAnn
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w v : V) :
    fderiv ℝ (_root_.GlobalTheory.RealWeil.gau : V → ℂ) w v =
      -(Real.pi : ℂ) * ⟪w, v⟫ * _root_.GlobalTheory.RealWeil.gau w := by sorry
