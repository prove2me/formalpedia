-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_mem_range_of_algebraMap_fixed
-- name    : GlobalTheory.FixedPoint.mem_range_of_algebraMap_fixed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:52:44.775561+00:00
-- url     : https://prove2.me/theorems/fc5397d8-751c-46da-8ae0-782a52c9b86a
-- title:
--   Fixed Point: mem range of algebra Map fixed
-- statement:
--   The Fixed Point construction uses the mem range of algebra Map fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
variable {K₀ : Type u} {K₁ : Type v} {L : Type w} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]

theorem GlobalTheory.FixedPoint.mem_range_of_algebraMap_fixed [PerfectField K₀] [IsAlgClosed L] (a : K₁)
    (ha : ∀ s : L ≃ₐ[K₀] L, s (algebraMap K₁ L a) = algebraMap K₁ L a) :
    a ∈ Set.range (algebraMap K₀ K₁) := by sorry
