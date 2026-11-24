-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_isCocomm_of_mul_comm
-- name    : GlobalTheory.FiniteFlatKilled.isCocomm_of_mul_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:24.748903+00:00
-- url     : https://prove2.me/theorems/c9165aab-a655-44b5-9da5-346051c9dba4
-- title:
--   Finite Flat Killed: is Cocomm of mul comm
-- statement:
--   The Finite Flat Killed construction uses the is Cocomm of mul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L186-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L186-L199

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

theorem GlobalTheory.FiniteFlatKilled.isCocomm_of_mul_comm {R B : Type*} [CommRing R] [CommRing B] [Bialgebra R B]
    (h : ∀ f g : WithConv (B →ₐ[R] B ⊗[R] B), f * g = g * f) : Coalgebra.IsCocomm R B := by sorry
