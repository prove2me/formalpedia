-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_nsmul_nsmul_eq_zero
-- name    : GroundTheory.Arith.Abelian.nsmul_nsmul_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:00.643104+00:00
-- url     : https://prove2.me/theorems/3720a766-0002-4a46-9b36-1d1f3e1f4de8
-- title:
--   Abelian: nsmul nsmul eq zero
-- statement:
--   The Abelian construction uses the nsmul nsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean#L38-L39

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

theorem GroundTheory.Arith.Abelian.nsmul_nsmul_eq_zero {P : A} (hP : N • P = 0) (a : ℕ) : N • a • P = 0 := by sorry
