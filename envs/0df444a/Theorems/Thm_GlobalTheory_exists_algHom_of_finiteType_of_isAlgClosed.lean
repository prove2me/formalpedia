-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_of_finiteType_of_isAlgClosed
-- name    : GlobalTheory.exists_algHom_of_finiteType_of_isAlgClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:38.232791+00:00
-- url     : https://prove2.me/theorems/563a9a35-d09d-5bdd-95f9-494a12b46103
-- title:
--   Global Theory: exists alg Hom of finite Type of is Alg Closed
-- statement:
--   The Global Theory construction uses the exists alg Hom of finite Type of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAlgHomOfFiniteTypeOfIsAlgClosed.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAlgHomOfFiniteTypeOfIsAlgClosed.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAlgHomOfFiniteTypeOfIsAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory

theorem GlobalTheory.exists_algHom_of_finiteType_of_isAlgClosed (K C F : Type) [Field K] [CommRing C]
    [Nontrivial C] [Algebra K C] [Algebra.FiniteType K C] [Field F] [IsAlgClosed F]
    [Algebra K F] : Nonempty (C →ₐ[K] F) := by sorry
