-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezout_gradedQuotDeg_bot_le
-- name    : GlobalTheory.GradedBezout.gradedQuotDeg_bot_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:30.040597+00:00
-- url     : https://prove2.me/theorems/dcde220d-1139-4abd-8235-e437f2c4bfe2
-- title:
--   Graded Bezout: graded Quot Deg bot le
-- statement:
--   The Graded Bezout construction uses the graded Quot Deg bot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L548-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L548-L565

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

theorem GlobalTheory.GradedBezout.gradedQuotDeg_bot_le {r : ℕ} {c : ℚ}
    (h : ∀ᶠ n : ℕ in atTop, (finrank K (𝒜 n) : ℚ) ≤ (c * n) ^ r) :
    gradedQuotDeg 𝒜 r ⊥ ≤ r.factorial * c ^ r := by sorry
