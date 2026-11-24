-- Prove2me | Theorems.Thm_GlobalTheory_isOfFinOrder_of_isOfFinOrder_mapRingHom
-- name    : GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:09.294623+00:00
-- url     : https://prove2.me/theorems/83fbbdcb-4eae-4356-aed8-8bdd78a82524
-- title:
--   Global Theory: is Of Fin Order of is Of Fin Order map Ring Hom
-- statement:
--   The Global Theory construction uses the is Of Fin Order of is Of Fin Order map Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHom.lean#L52-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderOfIsOfFinOrderMapRingHom.lean#L52-L70

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

theorem GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B']
    [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 →
    (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B,
    IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by sorry
