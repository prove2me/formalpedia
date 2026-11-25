-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezoutCount_card_le
-- name    : GlobalTheory.GradedBezoutCount.card_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:02:41.556262+00:00
-- url     : https://prove2.me/theorems/7076d33f-ba4f-55b8-84fe-0b5043fb3e1a
-- title:
--   Graded Bezout Count: card le
-- statement:
--   The Graded Bezout Count construction uses the card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L157-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L157-L181

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
open Classical

theorem GlobalTheory.GradedBezoutCount.card_le [IsAlgClosed K] {F : Set T} {a : ℕ} (ha : ∀ f ∈ F, f ∈ 𝒜 a)
    {Φ : Set (T →ₐ[K] K)} (hΦ : Φ.Finite)
    (hF : ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) →
      ∃ ψ ∈ Φ, ∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)
    {n : ℕ} (φ : Fin n → (T →ₐ[K] K)) (h1 : ∀ j, ∃ i, φ j (x i) ≠ 0)
    (h2 : ∀ j, ∀ f ∈ F, φ j f = 0)
    (h3 : ∀ j j', (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ j' y = c ^ e * φ j y) → j = j')
    (r : ℕ) (P : Ideal T) (hP : P.IsPrime) (hI : P.IsHomogeneous 𝒜)
    (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) :
    ((Finset.univ.filter fun j => ∀ y ∈ P, φ j y = 0).card : ℚ) ≤
      (a : ℚ) ^ r * gradedQuotDeg 𝒜 r P := by sorry
