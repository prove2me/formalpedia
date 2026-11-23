-- Prove2me | Theorems.Thm_GlobalTheory_exists_homogeneous_notMem_of_not_le
-- name    : GlobalTheory.exists_homogeneous_notMem_of_not_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:23.581969+00:00
-- url     : https://prove2.me/theorems/47a4d2a1-2e77-4d0e-a593-61077fdf6837
-- title:
--   Global Theory: exists homogeneous not Mem of not le
-- statement:
--   The Global Theory construction uses the exists homogeneous not Mem of not le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L23-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {A : Type*} [CommRing A] {τ : Type*} [SetLike τ A] [AddSubgroupClass τ A]
  (𝒜 : ℕ → τ) [GradedRing 𝒜]

theorem GlobalTheory.exists_homogeneous_notMem_of_not_le {J p : Ideal A} (hJ : J.IsHomogeneous 𝒜)
    (h : ¬ J ≤ p) : ∃ n, ∃ x ∈ 𝒜 n, x ∈ J ∧ x ∉ p := by sorry
