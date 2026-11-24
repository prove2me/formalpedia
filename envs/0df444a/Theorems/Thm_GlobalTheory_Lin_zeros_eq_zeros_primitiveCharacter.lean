-- Prove2me | Theorems.Thm_GlobalTheory_Lin_zeros_eq_zeros_primitiveCharacter
-- name    : GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:06:26.81181+00:00
-- url     : https://prove2.me/theorems/d5024178-fe52-4573-bdf4-684abc4add57
-- title:
--   Lin: zeros eq zeros primitive Character
-- statement:
--   The Lin construction uses the zeros eq zeros primitive Character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLZerosEqPrimitiveCharacterZeros.lean#L11-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLZerosEqPrimitiveCharacterZeros.lean#L11-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLZerosEqPrimitiveCharacterZeros
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical

theorem GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
      (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧
        _root_.GlobalTheory.Lin.ord χ s = _root_.GlobalTheory.Lin.ord χ.primitiveCharacter s := by sorry
