-- Prove2me | Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_sum_shift
-- name    : GlobalTheory.PrimeToNormalVanishing.sum_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:24.567909+00:00
-- url     : https://prove2.me/theorems/12c1f510-36e6-4086-8c96-30ba38d2bbc4
-- title:
--   Prime To Normal Vanishing: sum shift
-- statement:
--   The Prime To Normal Vanishing construction uses the sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCohomologyVanishesOfPrimeToLNormalNoIn.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCohomologyVanishesOfPrimeToLNormalNoIn.lean#L13-L17

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

theorem GlobalTheory.PrimeToNormalVanishing.sum_shift [hK : K.Normal] (φ : Q → M) (a k : Q) (hk : k ∈ K) :
    ∑ i : K, φ (k * (a * i)) = ∑ i : K, φ (a * i) := by sorry
