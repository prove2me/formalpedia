-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_exists_pow_eq_zero
-- name    : GlobalTheory.CompanionTheory.KWeightMajor.exists_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:40.653175+00:00
-- url     : https://prove2.me/theorems/a8abf3e0-a836-4485-8d8c-14da8c9b7443
-- title:
--   KWeight Major: exists pow eq zero
-- statement:
--   The KWeight Major construction uses the exists pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsPowEqZero.lean#L116-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsPowEqZero.lean#L116-L141

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_orthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KWeightMajor
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem GlobalTheory.CompanionTheory.KWeightMajor.exists_pow_eq_zero (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hzL : z ∈ L) (hz : IsWeight E μ z) :
    (∀ k : ℕ, (E a b ^ k) z ∈ L) ∧ ∃ k : ℕ, (E a b ^ k) z = 0 := by sorry
