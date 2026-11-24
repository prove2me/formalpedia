-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_exists_idele_section_of_ideal
-- name    : GlobalTheory.CMVal.exists_idele_section_of_ideal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:47.499229+00:00
-- url     : https://prove2.me/theorems/76977aa9-6e5d-4048-832d-ea70c5651525
-- title:
--   CMVal: exists idele section of ideal
-- statement:
--   The CMVal construction uses the exists idele section of ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L72-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory.CMVal.IdeleIdeal

theorem GlobalTheory.CMVal.exists_idele_section_of_ideal : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by sorry
