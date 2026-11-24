-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_exists_id_pow_eq_one_of_isFinite_of_flat
-- name    : GlobalTheory.FiniteFlatKilled.exists_id_pow_eq_one_of_isFinite_of_flat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:22.786022+00:00
-- url     : https://prove2.me/theorems/6f977cf4-b4b9-46ae-ba17-c2cc40c23766
-- title:
--   Finite Flat Killed: exists id pow eq one of is Finite of flat
-- statement:
--   The Finite Flat Killed construction uses the exists id pow eq one of is Finite of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L201-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L201-L240

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.FiniteFlatKilled.exists_id_pow_eq_one_of_isFinite_of_flat (R : Type) [CommRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H] (hf : IsFinite H.hom)
    (hfl : Flat H.hom) : ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 := by sorry
