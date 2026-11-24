-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_pairing_zero_left
-- name    : GroundTheory.Arith.Abelian.pairing_zero_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:26:43.327281+00:00
-- url     : https://prove2.me/theorems/184e9889-0d09-455a-87b4-6b37e0a7e65f
-- title:
--   Abelian: pairing zero left
-- statement:
--   The Abelian construction uses the pairing zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L20-L27

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

theorem GroundTheory.Arith.Abelian.pairing_zero_left
    (hl : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e (P + Q) R = e P R * e Q R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {R : A} (hR : N • R = 0) : e 0 R = 1 := by sorry
