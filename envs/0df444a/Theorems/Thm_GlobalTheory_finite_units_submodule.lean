-- Prove2me | Theorems.Thm_GlobalTheory_finite_units_submodule
-- name    : GlobalTheory.finite_units_submodule
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:13.604227+00:00
-- url     : https://prove2.me/theorems/35b1627a-a463-4fc5-9e90-1da3aa7be3ec
-- title:
--   Global Theory: finite units submodule
-- statement:
--   The Global Theory construction uses the finite units submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHom.lean#L24-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHom.lean#L24-L50

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

theorem GlobalTheory.finite_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Finite ℤ B'] (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range) :
    Finite (Submodule B B')ˣ := by sorry
