-- Prove2me | Theorems.Thm_GlobalTheory_exists_etale_subset_range
-- name    : GlobalTheory.exists_etale_subset_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:15.256725+00:00
-- url     : https://prove2.me/theorems/95c7d5a6-3014-4d44-a664-206d17642b3a
-- title:
--   Global Theory: exists etale subset range
-- statement:
--   The Global Theory construction uses the exists etale subset range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L181-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L181-L211

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
variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]

theorem GlobalTheory.exists_etale_subset_range [IsLocalRing B] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K]
    {ι : Type*} [Finite ι] (b : ι → K) :
    ∃ (P : StandardEtalePair B) (ε : P.Ring →ₐ[B] K), ∀ i, b i ∈ Set.range ε := by sorry
