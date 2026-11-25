-- Prove2me | Theorems.Thm_GlobalTheory_ContraRefl_res_apply
-- name    : GlobalTheory.ContraRefl.res_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:03.964834+00:00
-- url     : https://prove2.me/theorems/1f1c43bc-68fc-49c1-a6da-0bb4edda3c48
-- title:
--   Contra Refl: res apply
-- statement:
--   The Contra Refl construction uses the res apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L141-L142

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

theorem GlobalTheory.ContraRefl.res_apply (π : Representation ℂ G V) (K : Subgroup G) (l : fixed (contra π) K)
    (v : fixed π K) : res π K l v = ((l : smoothPart π.dual) : Module.Dual ℂ V) v := by sorry
