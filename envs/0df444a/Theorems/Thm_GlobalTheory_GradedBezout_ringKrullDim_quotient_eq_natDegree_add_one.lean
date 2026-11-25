-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezout_ringKrullDim_quotient_eq_natDegree_add_one
-- name    : GlobalTheory.GradedBezout.ringKrullDim_quotient_eq_natDegree_add_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:28.019103+00:00
-- url     : https://prove2.me/theorems/bcf7ffed-7d73-5b45-a8dc-49c5865787a8
-- title:
--   Graded Bezout: ring Krull Dim quotient eq nat Degree add one
-- statement:
--   The Graded Bezout construction uses the ring Krull Dim quotient eq nat Degree add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L485-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L485-L490

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
open GlobalTheory.GradedBezout
variable [GradedAlgebra 𝒜]
variable {𝒜}
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin

theorem GlobalTheory.GradedBezout.ringKrullDim_quotient_eq_natDegree_add_one {P : Ideal T} [P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) (h : ∃ i, x i ∉ P) :
    ringKrullDim (T ⧸ P) = ((gradedQuotHilbertPoly 𝒜 P).natDegree + 1 : ℕ) := by sorry
