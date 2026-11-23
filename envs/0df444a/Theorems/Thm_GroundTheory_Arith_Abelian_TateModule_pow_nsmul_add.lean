-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_TateModule_pow_nsmul_add
-- name    : GroundTheory.Arith.Abelian.TateModule.pow_nsmul_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:44.79809+00:00
-- url     : https://prove2.me/theorems/eb64562f-326c-4cbc-bff3-93c43f7c7d3e
-- title:
--   Tate Module: pow nsmul add
-- statement:
--   The Tate Module construction uses the pow nsmul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L32-L37

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
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
open AddSubgroup
variable (ℓ : ℕ) (A : Type*) [AddCommGroup A]
variable {ℓ A}

theorem GroundTheory.Arith.Abelian.TateModule.pow_nsmul_add (t : TateModule ℓ A) (i j : ℕ) :
    ℓ ^ j • (t : ℕ → A) (i + j) = (t : ℕ → A) i := by sorry
