-- Prove2me | Theorems.Thm_GlobalTheory_UnitCocycle_datum_apply
-- name    : GlobalTheory.UnitCocycle.datum_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:30.306294+00:00
-- url     : https://prove2.me/theorems/691124df-7990-4a83-b63a-7161b334ed4f
-- title:
--   Unit Cocycle: datum apply
-- statement:
--   The Unit Cocycle construction uses the datum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlat.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlat.lean#L32-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem GlobalTheory.UnitCocycle.datum_apply (c : B ⊗[R] B) (x : B) : datum c x = c * (x ⊗ₜ[R] (1 : B)) := by sorry
