-- Prove2me | Theorems.Thm_GlobalTheory_graded_bezout_step
-- name    : GlobalTheory.graded_bezout_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:40.188616+00:00
-- url     : https://prove2.me/theorems/42834993-b137-46d8-bc45-0a79a4bb014a
-- title:
--   Global Theory: graded bezout step
-- statement:
--   The Global Theory construction uses the graded bezout step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L571-L607
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L571-L607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module DirectSum
open GlobalTheory
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] (𝒜 : ℕ → Submodule K T)
open GradedBezout

theorem GlobalTheory.graded_bezout_step [GradedAlgebra 𝒜] {ι : Type*} [Finite ι] (x : ι → T)
    (hx : ∀ i, x i ∈ 𝒜 1) (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T) :
    (∀ J : Ideal T, J.IsHomogeneous 𝒜 →
      IsHilbertPoly (gradedQuotPiece 𝒜 J) (gradedQuotHilbertPoly 𝒜 J)) ∧
    ∀ (P : Ideal T) (r : ℕ), P.IsPrime → P.IsHomogeneous 𝒜 → (∃ i, x i ∉ P) →
      (gradedQuotHilbertPoly 𝒜 P).natDegree = r →
      (ringKrullDim (T ⧸ P) = (r + 1 : ℕ) ∧ ∃ D : ℕ, 1 ≤ D ∧ gradedQuotDeg 𝒜 r P = D) ∧
      ∀ (a : ℕ) (f : T), f ∈ 𝒜 a → f ∉ P →
        (P ⊔ Ideal.span {f}).minimalPrimes.Finite ∧
        (∀ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
          Q.IsHomogeneous 𝒜 ∧ ringKrullDim (T ⧸ Q) = r) ∧
        (1 ≤ r →
          (∀ Q ∈ relevantMinimalPrimes x (P ⊔ Ideal.span {f}),
            (gradedQuotHilbertPoly 𝒜 Q).natDegree = r - 1) ∧
          ∑ᶠ Q ∈ relevantMinimalPrimes x (P ⊔ Ideal.span {f}), gradedQuotDeg 𝒜 (r - 1) Q ≤
            a * gradedQuotDeg 𝒜 r P) := by sorry
