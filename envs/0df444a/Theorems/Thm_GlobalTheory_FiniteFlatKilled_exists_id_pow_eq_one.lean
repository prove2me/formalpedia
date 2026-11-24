-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_exists_id_pow_eq_one
-- name    : GlobalTheory.FiniteFlatKilled.exists_id_pow_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:21.816427+00:00
-- url     : https://prove2.me/theorems/bb929bd5-b1f6-4abd-ba09-2a408f08edda
-- title:
--   Finite Flat Killed: exists id pow eq one
-- statement:
--   The Finite Flat Killed construction uses the exists id pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L147-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L147-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
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
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open TensorProduct WithConv Coalgebra
variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]
variable [CommRing B] [HopfAlgebra R B]
variable [IsCocomm R B]

theorem GlobalTheory.FiniteFlatKilled.exists_id_pow_eq_one [Module.Finite R B] [Module.Flat R B] :
    ∃ N : ℕ, 1 ≤ N ∧ toConv (AlgHom.id R B) ^ N = 1 := by sorry
