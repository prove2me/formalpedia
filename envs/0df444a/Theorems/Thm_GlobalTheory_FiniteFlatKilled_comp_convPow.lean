-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_comp_convPow
-- name    : GlobalTheory.FiniteFlatKilled.comp_convPow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:01.625942+00:00
-- url     : https://prove2.me/theorems/f1a2b514-56c7-40eb-965f-c0f1a36fcd40
-- title:
--   Finite Flat Killed: comp conv Pow
-- statement:
--   The Finite Flat Killed construction uses the comp conv Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L141-L145

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

theorem GlobalTheory.FiniteFlatKilled.comp_convPow (h : C →ₐ[R] F) (f : WithConv (B →ₐ[R] C)) (n : ℕ) :
    h.comp (f ^ n).ofConv = (toConv (h.comp f.ofConv) ^ n).ofConv := by sorry
