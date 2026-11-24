-- Prove2me | Theorems.Thm_GlobalTheory_MulCocycle_mem_map_algebraMap_iff
-- name    : GlobalTheory.MulCocycle.mem_map_algebraMap_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:47.68066+00:00
-- url     : https://prove2.me/theorems/a538d0af-48ce-40c8-a8b7-df231ebf4209
-- title:
--   Mul Cocycle: mem map algebra Map iff
-- statement:
--   The Mul Cocycle construction uses the mem map algebra Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnitCoboundaryOfMulCocycle.lean#L45-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnitCoboundaryOfMulCocycle.lean#L45-L62

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

theorem GlobalTheory.MulCocycle.mem_map_algebraMap_iff (J : Ideal B) (b : B[X]) :
    b ∈ J.map (algebraMap B B[X]) ↔ ∀ x, b.coeff x ∈ J := by sorry
