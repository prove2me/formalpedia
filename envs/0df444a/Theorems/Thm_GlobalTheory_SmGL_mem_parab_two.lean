-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_mem_parab_two
-- name    : GlobalTheory.SmGL.mem_parab_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:55.631214+00:00
-- url     : https://prove2.me/theorems/069a81fd-5860-4b3f-9c22-384bcb13c303
-- title:
--   Sm GL: mem parab two
-- statement:
--   The Sm GL construction uses the mem parab two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L635-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L635-L647

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
omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem GlobalTheory.SmGL.mem_parab_two {e : a ⊕ b ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two e) ↔
      ∀ (j : b) (i : a), (g : Matrix n n R) (e (.inr j)) (e (.inl i)) = 0 := by sorry
