-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_nsmul_zmod_eq_zero_iff_dvd
-- name    : GlobalTheory.WpFam.nsmul_zmod_eq_zero_iff_dvd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:09.383139+00:00
-- url     : https://prove2.me/theorems/bec8ca46-3644-4c33-a1dc-ef79fab918e3
-- title:
--   Wp Fam: nsmul zmod eq zero iff dvd
-- statement:
--   The Wp Fam construction uses the nsmul zmod eq zero iff dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastMulTorsMemLatticeIff.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastMulTorsMemLatticeIff.lean#L9-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastMulTorsMemLatticeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.nsmul_zmod_eq_zero_iff_dvd (N : ℕ) [NeZero N] (M : ℕ) (a : ZMod N) :
    M • a = 0 ↔ N ∣ M * a.val := by sorry
