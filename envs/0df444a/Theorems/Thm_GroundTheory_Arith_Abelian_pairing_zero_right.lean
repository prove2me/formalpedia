-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_pairing_zero_right
-- name    : GroundTheory.Arith.Abelian.pairing_zero_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:54.752352+00:00
-- url     : https://prove2.me/theorems/97ab1f87-bcb7-4ca5-a4da-ea19911fc06b
-- title:
--   Abelian: pairing zero right
-- statement:
--   The Abelian construction uses the pairing zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L29-L36

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

theorem GroundTheory.Arith.Abelian.pairing_zero_right
    (hr : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e P (Q + R) = e P Q * e P R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P : A} (hP : N • P = 0) : e P 0 = 1 := by sorry
