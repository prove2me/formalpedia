-- Prove2me | Theorems.Thm_GlobalTheory_Serre_mulChar_tmul
-- name    : GlobalTheory.Serre.mulChar_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:35.386073+00:00
-- url     : https://prove2.me/theorems/e4f5fc8b-5e54-4d37-a630-3e1062bf17a9
-- title:
--   Serre: mul Char tmul
-- statement:
--   The Serre construction uses the mul Char tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L21-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]

theorem GlobalTheory.Serre.mulChar_tmul (r : R) (x : O') :
    mulChar R O O' (r ⊗ₜ x) = r * algebraMap O' R x := by sorry

attribute [defeq] GlobalTheory.Serre.mulChar_tmul
