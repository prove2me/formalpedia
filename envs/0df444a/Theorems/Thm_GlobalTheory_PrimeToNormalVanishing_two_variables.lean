-- Prove2me | Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_two_variables
-- name    : GlobalTheory.PrimeToNormalVanishing.two_variables
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:57.414196+00:00
-- url     : https://prove2.me/theorems/0031049b-5d9c-43eb-a65d-30d8267c7963
-- title:
--   Prime To Normal Vanishing: two variables
-- statement:
--   The Prime To Normal Vanishing construction uses the two variables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCohomologyVanishesOfPrimeToLNormalNoIn.lean#L19-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCohomologyVanishesOfPrimeToLNormalNoIn.lean#L19-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PrimeToNormalVanishing
variable {G Q R M : Type} [Group G] [Group Q] [CommRing R] [AddCommGroup M] [Module R M]
  (ρ : Representation R G M) (π : G →* Q) (J : Subgroup G) (K : Subgroup Q) [Fintype K]

theorem GlobalTheory.PrimeToNormalVanishing.two_variables [K.Normal] (hJK : ∀ j ∈ J, π j ∈ K)
    (hinv : ∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) (F : Q → Q → M)
    (heq : ∀ g a b, F (π g * a) (π g * b) = ρ g (F a b))
    (hc : ∀ a b c, F b c - F a c + F a b = 0) :
    ∃ m : M, ∀ g, (Fintype.card K) ^ 2 • F 1 (π g) = ρ g m - m := by sorry
