-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezout_exists_pos_nat_gradedQuotDeg_eq
-- name    : GlobalTheory.GradedBezout.exists_pos_nat_gradedQuotDeg_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:50:53.307734+00:00
-- url     : https://prove2.me/theorems/46adf4be-e406-4807-8cc2-9fe0953fd040
-- title:
--   Graded Bezout: exists pos nat graded Quot Deg eq
-- statement:
--   The Graded Bezout construction uses the exists pos nat graded Quot Deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L504-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L504-L512

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

theorem GlobalTheory.GradedBezout.exists_pos_nat_gradedQuotDeg_eq {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜)
    {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) :
    ∃ D : ℕ, 1 ≤ D ∧ gradedQuotDeg 𝒜 r P = D := by sorry
