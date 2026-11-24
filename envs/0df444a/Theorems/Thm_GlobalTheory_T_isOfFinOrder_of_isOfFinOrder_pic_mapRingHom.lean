-- Prove2me | Theorems.Thm_GlobalTheory_T_isOfFinOrder_of_isOfFinOrder_pic_mapRingHom
-- name    : GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:11.29386+00:00
-- url     : https://prove2.me/theorems/8d88428f-eb59-40d5-8c2c-a6f93785001c
-- title:
--   T: is Of Fin Order of is Of Fin Order pic map Ring Hom
-- statement:
--   The T construction uses the is Of Fin Order of is Of Fin Order pic map Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHomStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHomStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 → (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B, IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by sorry
