-- Prove2me | Theorems.Thm_GlobalTheory_surjective_spMap_of_field
-- name    : GlobalTheory.surjective_spMap_of_field
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:49.595183+00:00
-- url     : https://prove2.me/theorems/a578c797-a364-42ba-884c-184b8bfdb414
-- title:
--   Global Theory: surjective sp Map of field
-- statement:
--   The Global Theory construction uses the surjective sp Map of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackFieldOfIrreducibleCover.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackFieldOfIrreducibleCover.lean#L27-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackFieldOfIrreducibleCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.surjective_spMap_of_field {F k : Type} [Field F] [Field k] (f : F →+* k) :
    Surjective (spMap f) := by sorry
