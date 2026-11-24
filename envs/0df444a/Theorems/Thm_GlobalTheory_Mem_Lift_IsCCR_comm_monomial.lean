-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_IsCCR_comm_monomial
-- name    : GlobalTheory.Mem.Lift.IsCCR.comm_monomial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:58.231365+00:00
-- url     : https://prove2.me/theorems/9951b9c4-3067-42fd-9abf-b26963e22a4b
-- title:
--   Is CCR: comm monomial
-- statement:
--   The Is CCR construction uses the comm monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlRelOfCanonicalCommutationRelations.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlRelOfCanonicalCommutationRelations.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlRelOfCanonicalCommutationRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift

theorem GlobalTheory.Mem.Lift.IsCCR.comm_monomial {A : Type} [Ring A] {κ : Type} [DecidableEq κ] {x d : κ → A} (h : IsCCR x d)
    (k l k' l' : κ) : x k * d l * (x k' * d l') - x k' * d l' * (x k * d l) =
      (if k' = l then x k * d l' else 0) - (if k = l' then x k' * d l else 0) := by sorry
