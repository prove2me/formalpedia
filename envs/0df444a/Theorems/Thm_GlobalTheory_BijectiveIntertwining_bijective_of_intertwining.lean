-- Prove2me | Theorems.Thm_GlobalTheory_BijectiveIntertwining_bijective_of_intertwining
-- name    : GlobalTheory.BijectiveIntertwining.bijective_of_intertwining
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:01:17.195277+00:00
-- url     : https://prove2.me/theorems/60ff37bf-0840-4355-8e2d-750f721e64e6
-- title:
--   Bijective Intertwining: bijective of intertwining
-- statement:
--   The Bijective Intertwining construction uses the bijective of intertwining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/BijectiveOfIntertwining.lean#L5-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/BijectiveOfIntertwining.lean#L5-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_BijectiveOfIntertwining
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BijectiveIntertwining

theorem GlobalTheory.BijectiveIntertwining.bijective_of_intertwining {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (h : Representation.IsIrreducible ρ) (h' : Representation.IsIrreducible ρ')
    (F : V →ₗ[ℂ] V') (hF : ∀ (g : G) (v : V), F (ρ g v) = ρ' g (F v)) (h0 : F ≠ 0) :
    Function.Bijective F := by sorry
