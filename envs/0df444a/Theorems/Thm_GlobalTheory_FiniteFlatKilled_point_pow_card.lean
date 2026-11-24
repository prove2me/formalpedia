-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_point_pow_card
-- name    : GlobalTheory.FiniteFlatKilled.point_pow_card
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:15.481902+00:00
-- url     : https://prove2.me/theorems/1afba68b-2ed3-4fcf-8607-1f7c73d4a8c3
-- title:
--   Finite Flat Killed: point pow card
-- statement:
--   The Finite Flat Killed construction uses the point pow card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L96-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L96-L139

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

theorem GlobalTheory.FiniteFlatKilled.point_pow_card {ι : Type*} [Fintype ι] (b : Module.Basis ι C (C ⊗[R] B))
    (u : B →ₐ[R] C) : toConv u ^ Fintype.card ι = 1 := by sorry
