-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_mul_comp_antipode
-- name    : GlobalTheory.FiniteFlatKilled.mul_comp_antipode
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:21.489613+00:00
-- url     : https://prove2.me/theorems/c3390fe5-e358-4ab4-9333-6ec9a32d338c
-- title:
--   Finite Flat Killed: mul comp antipode
-- statement:
--   The Finite Flat Killed construction uses the mul comp antipode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L82-L92

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

theorem GlobalTheory.FiniteFlatKilled.mul_comp_antipode (u : B →ₐ[R] C) :
    toConv u * toConv (u.comp (HopfAlgebra.antipodeAlgHom R B)) = 1 := by sorry
