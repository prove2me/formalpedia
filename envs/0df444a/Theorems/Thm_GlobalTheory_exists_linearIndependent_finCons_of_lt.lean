-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearIndependent_finCons_of_lt
-- name    : GlobalTheory.exists_linearIndependent_finCons_of_lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:17.082777+00:00
-- url     : https://prove2.me/theorems/f93ec512-e13c-4f38-b2e3-ecbd2c2789cb
-- title:
--   Global Theory: exists linear Independent fin Cons of lt
-- statement:
--   The Global Theory construction uses the exists linear Independent fin Cons of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentAdaptedToDecreasingChainA.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentAdaptedToDecreasingChainA.lean#L7-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentAdaptedToDecreasingChainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.exists_linearIndependent_finCons_of_lt {G : Type} [AddCommGroup G] {m k : ℕ}
    (e : Fin m → G) (he : LinearIndependent ℤ e) (f : Fin k → G) (hf : LinearIndependent ℤ f)
    (hmk : m < k) : ∃ j, LinearIndependent ℤ (Fin.cons (f j) e : Fin m.succ → G) := by sorry
