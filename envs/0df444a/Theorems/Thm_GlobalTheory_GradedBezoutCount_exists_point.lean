-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezoutCount_exists_point
-- name    : GlobalTheory.GradedBezoutCount.exists_point
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:55.398537+00:00
-- url     : https://prove2.me/theorems/5b129925-a219-56ef-9288-76081355909d
-- title:
--   Graded Bezout Count: exists point
-- statement:
--   The Graded Bezout Count construction uses the exists point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L48-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GradedBezoutCount
open GradedBezout
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] {𝒜 : ℕ → Submodule K T}
  [GradedAlgebra 𝒜]
omit [GradedAlgebra 𝒜]

theorem GlobalTheory.GradedBezoutCount.exists_point [IsAlgClosed K] [Algebra.FiniteType K T] {P : Ideal T} [hP : P.IsPrime]
    {h : T} (hh : h ∉ P) : ∃ φ : T →ₐ[K] K, (∀ y ∈ P, φ y = 0) ∧ φ h ≠ 0 := by sorry
