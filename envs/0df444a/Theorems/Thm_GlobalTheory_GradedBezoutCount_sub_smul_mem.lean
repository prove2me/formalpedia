-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezoutCount_sub_smul_mem
-- name    : GlobalTheory.GradedBezoutCount.sub_smul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:29.862041+00:00
-- url     : https://prove2.me/theorems/57017746-50d3-4104-be3e-f4042112ae30
-- title:
--   Graded Bezout Count: sub smul mem
-- statement:
--   The Graded Bezout Count construction uses the sub smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L16-L20

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

theorem GlobalTheory.GradedBezoutCount.sub_smul_mem (φ : T →ₐ[K] K) {t y : T} {e : ℕ} (ht : t ∈ 𝒜 1) (hy : y ∈ 𝒜 e) :
    φ t ^ e • y - φ y • t ^ e ∈ 𝒜 e ∧ φ (φ t ^ e • y - φ y • t ^ e) = 0 := by sorry
