-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_pairing_ne_zero
-- name    : GroundTheory.Arith.Abelian.pairing_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:51.229748+00:00
-- url     : https://prove2.me/theorems/3189c22a-c2fe-431c-9f8d-4c66e90be700
-- title:
--   Abelian: pairing ne zero
-- statement:
--   The Abelian construction uses the pairing ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open PadicInt
variable {A : Type*} [AddCommGroup A] {L : Type*} [Field L] (N : ℕ) (e : A → A → L)

theorem GroundTheory.Arith.Abelian.pairing_ne_zero (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P Q : A} (hP : N • P = 0) (hQ : N • Q = 0) : e P Q ≠ 0 := by sorry
