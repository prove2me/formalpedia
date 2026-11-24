-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_map
-- name    : GlobalTheory.ThetaGL.DualPair.ev_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:54.983259+00:00
-- url     : https://prove2.me/theorems/f6be2595-ee19-4db6-944b-de09b22ad889
-- title:
--   Dual Pair: ev map
-- statement:
--   The Dual Pair construction uses the ev map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L123-L129

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

theorem GlobalTheory.ThetaGL.DualPair.ev_map {H : Type} [Group H] (σ : Representation ℂ H V) (π : Representation ℂ G W) (g : H) (h : G)
    (t : V ⊗[ℂ] smoothPart π.dual) (w : W) :
    ev V π (TensorProduct.map (σ g) (contra π h) t) w = σ g (ev V π t (π h⁻¹ w)) := by sorry
