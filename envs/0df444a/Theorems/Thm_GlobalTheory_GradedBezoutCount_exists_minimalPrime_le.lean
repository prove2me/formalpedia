-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezoutCount_exists_minimalPrime_le
-- name    : GlobalTheory.GradedBezoutCount.exists_minimalPrime_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:49.252636+00:00
-- url     : https://prove2.me/theorems/e1a5900a-8570-597f-ac22-dd43b3fae8fb
-- title:
--   Graded Bezout Count: exists minimal Prime le
-- statement:
--   The Graded Bezout Count construction uses the exists minimal Prime le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L97-L102

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
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
omit hx [GradedAlgebra 𝒜] [Finite ι] hfin

theorem GlobalTheory.GradedBezoutCount.exists_minimalPrime_le {P : Ideal T} {f : T} (φ : T →ₐ[K] K) (hP : ∀ y ∈ P, φ y = 0)
    (hf : φ f = 0) : ∃ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes, ∀ y ∈ Q, φ y = 0 := by sorry
