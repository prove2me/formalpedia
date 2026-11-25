-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezoutCount_exists_notMem
-- name    : GlobalTheory.GradedBezoutCount.exists_notMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:06.015503+00:00
-- url     : https://prove2.me/theorems/209ee076-22b5-4238-80a2-263fbe0867cc
-- title:
--   Graded Bezout Count: exists not Mem
-- statement:
--   The Graded Bezout Count construction uses the exists not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L66-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L66-L94

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

theorem GlobalTheory.GradedBezoutCount.exists_notMem [IsAlgClosed K] {F : Set T} {Φ : Set (T →ₐ[K] K)} (hΦ : Φ.Finite)
    (hF : ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) →
      ∃ ψ ∈ Φ, ∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)
    {P : Ideal T} [hP : P.IsPrime] {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 2 : ℕ)) :
    ∃ f ∈ F, f ∉ P := by sorry
