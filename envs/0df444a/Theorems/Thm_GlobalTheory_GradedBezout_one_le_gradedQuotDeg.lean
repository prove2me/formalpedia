-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezout_one_le_gradedQuotDeg
-- name    : GlobalTheory.GradedBezout.one_le_gradedQuotDeg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:50:25.531022+00:00
-- url     : https://prove2.me/theorems/9e4cab87-05e3-5aea-a77e-0725df8dcbc8
-- title:
--   Graded Bezout: one le graded Quot Deg
-- statement:
--   The Graded Bezout construction uses the one le graded Quot Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L514-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L514-L518

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

theorem GlobalTheory.GradedBezout.one_le_gradedQuotDeg {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜)
    {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) : 1 ≤ gradedQuotDeg 𝒜 r P := by sorry
