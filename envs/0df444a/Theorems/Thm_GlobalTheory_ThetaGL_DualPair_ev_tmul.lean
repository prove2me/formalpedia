-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_tmul
-- name    : GlobalTheory.ThetaGL.DualPair.ev_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:08.87624+00:00
-- url     : https://prove2.me/theorems/497cc186-acbe-4940-b099-1f3334d3e04d
-- title:
--   Dual Pair: ev tmul
-- statement:
--   The Dual Pair construction uses the ev tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L30-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaGL GlobalTheory.ThetaGL.DualPair
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.ThetaGL.DualPair.ev_tmul (π : Representation ℂ G W) (v : V) (l : smoothPart π.dual) (w : W) :
    ev V π (v ⊗ₜ l) w = (l : Module.Dual ℂ W) w • v := by sorry

attribute [defeq] GlobalTheory.ThetaGL.DualPair.ev_tmul
