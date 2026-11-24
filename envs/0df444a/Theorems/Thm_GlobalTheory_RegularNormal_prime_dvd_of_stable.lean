-- Prove2me | Theorems.Thm_GlobalTheory_RegularNormal_prime_dvd_of_stable
-- name    : GlobalTheory.RegularNormal.prime_dvd_of_stable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:54.791015+00:00
-- url     : https://prove2.me/theorems/d0b73214-42d1-42f2-b2ad-ed098ce70af2
-- title:
--   Regular Normal: prime dvd of stable
-- statement:
--   The Regular Normal construction uses the prime dvd of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L70-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.RegularNormal
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
omit [IsLocalRing A]

theorem GlobalTheory.RegularNormal.prime_dvd_of_stable (hx : Prime x) {a b : A} {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = x * b * s) : x ∣ a := by sorry
