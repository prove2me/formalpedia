-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_pow_card_eq_one
-- name    : GlobalTheory.FiniteFlatKilled.pow_card_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:24.46586+00:00
-- url     : https://prove2.me/theorems/2b20d892-4e09-40dc-acf9-8bc3db4831d3
-- title:
--   Finite Flat Killed: pow card eq one
-- statement:
--   The Finite Flat Killed construction uses the pow card eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L37-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L37-L76

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
variable [AddCommGroup B] [Module R B] [Coalgebra R B] [IsCocomm R B]
variable [Algebra C F] [IsScalarTower R C F]

theorem GlobalTheory.FiniteFlatKilled.pow_card_eq_one {ι : Type*} [Fintype ι] (b : Module.Basis ι C F) (τ : F ≃ₐ[C] F)
    (x : WithConv (B →ₗ[R] F)) (hx : IsUnit x) (u : WithConv (B →ₗ[R] C))
    (h : postcomp B (τ.toAlgHom.restrictScalars R) x =
      x * postcomp B (IsScalarTower.toAlgHom R C F) u) :
    u ^ Fintype.card ι = 1 := by sorry
