-- Prove2me | Theorems.Thm_GlobalTheory_natCast_mul_mem_units_submodule
-- name    : GlobalTheory.natCast_mul_mem_units_submodule
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:09.825539+00:00
-- url     : https://prove2.me/theorems/a68259f1-7b85-4a10-98e7-fc230b7f5948
-- title:
--   Global Theory: nat Cast mul mem units submodule
-- statement:
--   The Global Theory construction uses the nat Cast mul mem units submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHom.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHom.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CommRing

theorem GlobalTheory.natCast_mul_mem_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (n : ℕ) (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range)
    (I : (Submodule B B')ˣ) (x : B') : (n : B') * x ∈ (I : Submodule B B') := by sorry
