-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezout_exists_ringKrullDim_quotient_eq_succ
-- name    : GlobalTheory.GradedBezout.exists_ringKrullDim_quotient_eq_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:19.934539+00:00
-- url     : https://prove2.me/theorems/74f59a95-f638-4e9f-bbdb-5c1aac9aad76
-- title:
--   Graded Bezout: exists ring Krull Dim quotient eq succ
-- statement:
--   The Graded Bezout construction uses the exists ring Krull Dim quotient eq succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L476-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L476-L483

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

theorem GlobalTheory.GradedBezout.exists_ringKrullDim_quotient_eq_succ {P : Ideal T} [hP : P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) {i : ι} (h : x i ∉ P) :
    ∃ e : ℕ, ringKrullDim (T ⧸ P) = (e + 1 : ℕ) := by sorry
