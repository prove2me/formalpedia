-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_coe_mem_unipRad
-- name    : GlobalTheory.SmGL.coe_mem_unipRad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:33.56908+00:00
-- url     : https://prove2.me/theorems/0f774d8a-c53d-43dd-81d1-af13d702af7a
-- title:
--   Sm GL: coe mem unip Rad
-- statement:
--   The Sm GL construction uses the coe mem unip Rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L273-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L273-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)

theorem GlobalTheory.SmGL.coe_mem_unipRad {e : (Σ a, m a) ≃ n}
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    (p : GL n R) ∈ _root_.GlobalTheory.SmGL.unipRad R e ↔ _root_.GlobalTheory.SmGL.leviProj R e p = 1 := by sorry
