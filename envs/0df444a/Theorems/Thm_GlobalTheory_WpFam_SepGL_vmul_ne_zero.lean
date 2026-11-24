-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_SepGL_vmul_ne_zero
-- name    : GlobalTheory.WpFam.SepGL.vmul_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:54.105014+00:00
-- url     : https://prove2.me/theorems/414b7445-3433-44c5-b5c1-4c009d1f1923
-- title:
--   Sep GL: vmul ne zero
-- statement:
--   The Sep GL construction uses the vmul ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VmulNeZero.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VmulNeZero.lean#L10-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VmulNeZero
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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.SepGL

theorem GlobalTheory.WpFam.SepGL.vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by sorry
