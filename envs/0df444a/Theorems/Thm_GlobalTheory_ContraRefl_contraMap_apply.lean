-- Prove2me | Theorems.Thm_GlobalTheory_ContraRefl_contraMap_apply
-- name    : GlobalTheory.ContraRefl.contraMap_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:39.48019+00:00
-- url     : https://prove2.me/theorems/7cd088a7-72c8-4f6d-936f-92ff5037d43f
-- title:
--   Contra Refl: contra Map apply
-- statement:
--   The Contra Refl construction uses the contra Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L350-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L350-L353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.ContraRefl.contraMap_apply {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ G X} {τ : Representation ℂ G Y} (f : σ.IntertwiningMap τ)
    (l : smoothPart τ.dual) (x : X) :
    (contraMap f l : Module.Dual ℂ X) x = (l : Module.Dual ℂ Y) (f x) := by sorry
