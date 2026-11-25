-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezoutCount_card_le_step
-- name    : GlobalTheory.GradedBezoutCount.card_le_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:03.010095+00:00
-- url     : https://prove2.me/theorems/f1d27e3d-79c4-429a-8df9-ca3e15c4f058
-- title:
--   Graded Bezout Count: card le step
-- statement:
--   The Graded Bezout Count construction uses the card le step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L128-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientLeOne.lean#L128-L153

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

theorem GlobalTheory.GradedBezoutCount.card_le_step {n : ℕ} (φ : Fin n → (T →ₐ[K] K)) {P : Ideal T} [P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 2 : ℕ)) {f : T} {b : ℕ}
    (hf : f ∈ 𝒜 b) (hfP : f ∉ P) (h0 : ∀ j, φ j f = 0) {B : ℚ} (hB : 0 ≤ B)
    (h : ∀ Q : Ideal T, Q.IsPrime → Q.IsHomogeneous 𝒜 → ringKrullDim (T ⧸ Q) = (r + 1 : ℕ) →
      ((Finset.univ.filter fun j => ∀ y ∈ Q, φ j y = 0).card : ℚ) ≤ B * gradedQuotDeg 𝒜 r Q) :
    ((Finset.univ.filter fun j => ∀ y ∈ P, φ j y = 0).card : ℚ) ≤
      B * (b * gradedQuotDeg 𝒜 (r + 1) P) := by sorry
