-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_VacAnn_proj_annihilated
-- name    : GlobalTheory.Mem.Lift.VacAnn.proj_annihilated
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:49.550081+00:00
-- url     : https://prove2.me/theorems/9252df3f-b335-452e-90ef-155f8dc6e5ac
-- title:
--   Vac Ann: proj annihilated
-- statement:
--   The Vac Ann construction uses the proj annihilated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VacuumProjectorRangeAnnihilated.lean#L46-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VacuumProjectorRangeAnnihilated.lean#L46-L86

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

theorem GlobalTheory.Mem.Lift.VacAnn.proj_annihilated : ∀ (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V)
    (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) →
    ∀ (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (x : B) (z : V),
      _root_.GlobalTheory.Mem.Lift.dH ρ z (_root_.GlobalTheory.RealWeil.proj h x) +
        I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) (_root_.GlobalTheory.RealWeil.proj h x) = 0 := by sorry
