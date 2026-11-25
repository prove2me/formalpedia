-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_pairing_nsmul_right
-- name    : GroundTheory.Arith.Abelian.pairing_nsmul_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:26:39.534943+00:00
-- url     : https://prove2.me/theorems/aa23946a-7768-42ba-8659-2bfa87c4a65f
-- title:
--   Abelian: pairing nsmul right
-- statement:
--   The Abelian construction uses the pairing nsmul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L50-L57

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

theorem GroundTheory.Arith.Abelian.pairing_nsmul_right
    (hr : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e P (Q + R) = e P Q * e P R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P R : A} (hP : N • P = 0) (hR : N • R = 0) (a : ℕ) : e P (a • R) = e P R ^ a := by sorry
