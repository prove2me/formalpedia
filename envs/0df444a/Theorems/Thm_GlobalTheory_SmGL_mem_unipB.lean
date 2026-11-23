-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_mem_unipB
-- name    : GlobalTheory.SmGL.mem_unipB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:48.012033+00:00
-- url     : https://prove2.me/theorems/903c2476-40bd-42f4-b5cb-2fa20bdf9a61
-- title:
--   Sm GL: mem unip B
-- statement:
--   The Sm GL construction uses the mem unip B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L772-L782
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L772-L782

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
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem GlobalTheory.SmGL.mem_unipB {n : Type} [Fintype n] [DecidableEq n]
    [LinearOrder n] {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipB R n ↔
      (∀ i j, j < i → (g : Matrix n n R) i j = 0) ∧ ∀ i, (g : Matrix n n R) i i = 1 := by sorry
