-- Prove2me | Theorems.Thm_GlobalTheory_GradedBezout_ringKrullDim_quotient_of_mem_minimalPrimes_sup
-- name    : GlobalTheory.GradedBezout.ringKrullDim_quotient_of_mem_minimalPrimes_sup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:15.245198+00:00
-- url     : https://prove2.me/theorems/7e21ec1b-8e8e-496a-abdd-46238a5d3eb5
-- title:
--   Graded Bezout: ring Krull Dim quotient of mem minimal Primes sup
-- statement:
--   The Graded Bezout construction uses the ring Krull Dim quotient of mem minimal Primes sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L522-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimQuotientOfMemMinimalPrimesSup.lean#L522-L530

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
omit hx [GradedAlgebra 𝒜]

theorem GlobalTheory.GradedBezout.ringKrullDim_quotient_of_mem_minimalPrimes_sup {P Q : Ideal T} [P.IsPrime] {r : ℕ}
    (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) {f : T} (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ringKrullDim (T ⧸ Q) = r := by sorry
