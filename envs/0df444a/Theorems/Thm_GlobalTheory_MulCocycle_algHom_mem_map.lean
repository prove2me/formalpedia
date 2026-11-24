-- Prove2me | Theorems.Thm_GlobalTheory_MulCocycle_algHom_mem_map
-- name    : GlobalTheory.MulCocycle.algHom_mem_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:08.33484+00:00
-- url     : https://prove2.me/theorems/43efd1d5-2550-4204-9951-ce69297ccc90
-- title:
--   Mul Cocycle: alg Hom mem map
-- statement:
--   The Mul Cocycle construction uses the alg Hom mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnitCoboundaryOfMulCocycle.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnitCoboundaryOfMulCocycle.lean#L64-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.MulCocycle
variable {B : Type*} [CommRing B] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

theorem GlobalTheory.MulCocycle.algHom_mem_map {C C' : Type*} [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
    {J : Ideal B} (φ : C →ₐ[B] C') {a : C} (ha : a ∈ J.map (algebraMap B C)) :
    φ a ∈ J.map (algebraMap B C') := by sorry
