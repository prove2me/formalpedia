-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezout_sum_coeff_hilbertPoly_le
-- name    : GlobalTheory.GradedBezout.sum_coeff_hilbertPoly_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:50:18.615384+00:00
-- url     : https://prove2.me/theorems/99477edd-65bb-4fb6-aec2-f50f378b4a88
-- title:
--   Graded Bezout: sum coeff hilbert Poly le
-- statement:
--   The Graded Bezout construction uses the sum coeff hilbert Poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L438-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L438-L474

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

theorem GlobalTheory.GradedBezout.sum_coeff_hilbertPoly_le {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {e : ℕ}
    (he : (gradedQuotHilbertPoly 𝒜 I).degree ≤ e) (s : Finset (Ideal T))
    (hs : ∀ Q ∈ s, Q ∈ I.minimalPrimes) :
    ∑ Q ∈ s, (gradedQuotHilbertPoly 𝒜 Q).coeff e ≤ (gradedQuotHilbertPoly 𝒜 I).coeff e := by sorry
