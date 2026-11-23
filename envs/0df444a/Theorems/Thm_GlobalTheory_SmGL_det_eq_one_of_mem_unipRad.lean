-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_det_eq_one_of_mem_unipRad
-- name    : GlobalTheory.SmGL.det_eq_one_of_mem_unipRad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:09.776928+00:00
-- url     : https://prove2.me/theorems/cdbc1133-fb8a-4f0b-bc9b-516a6d3b0d9b
-- title:
--   Sm GL: det eq one of mem unip Rad
-- statement:
--   The Sm GL construction uses the det eq one of mem unip Rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L361-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L361-L366

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

theorem GlobalTheory.SmGL.det_eq_one_of_mem_unipRad {e : (Σ a, m a) ≃ n} {u : GL n R}
    (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) : GeneralLinearGroup.det u = 1 := by sorry
