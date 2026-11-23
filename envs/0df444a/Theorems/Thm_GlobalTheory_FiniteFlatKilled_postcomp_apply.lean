-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_postcomp_apply
-- name    : GlobalTheory.FiniteFlatKilled.postcomp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:32.614725+00:00
-- url     : https://prove2.me/theorems/a371edbc-b867-40f6-bcb3-12bdc36ec3a8
-- title:
--   Finite Flat Killed: postcomp apply
-- statement:
--   The Finite Flat Killed construction uses the postcomp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L32-L33

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

theorem GlobalTheory.FiniteFlatKilled.postcomp_apply (h : C →ₐ[R] F) (f : WithConv (B →ₗ[R] C)) (c : B) :
    postcomp B h f c = h (f c) := by sorry

attribute [defeq] GlobalTheory.FiniteFlatKilled.postcomp_apply
