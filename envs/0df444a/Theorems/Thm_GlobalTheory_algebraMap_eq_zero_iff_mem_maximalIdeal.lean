-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_eq_zero_iff_mem_maximalIdeal
-- name    : GlobalTheory.algebraMap_eq_zero_iff_mem_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:18.896611+00:00
-- url     : https://prove2.me/theorems/80fb1121-3ce8-43ce-a848-6f4836bf0269
-- title:
--   Global Theory: algebra Map eq zero iff mem maximal Ideal
-- statement:
--   The Global Theory construction uses the algebra Map eq zero iff mem maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L273-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L273-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
universe u
variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [IsLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
omit [Algebra B W] [CommRing W]

theorem GlobalTheory.algebraMap_eq_zero_iff_mem_maximalIdeal (b : B) :
    algebraMap B K b = 0 ↔ b ∈ maximalIdeal B := by sorry
