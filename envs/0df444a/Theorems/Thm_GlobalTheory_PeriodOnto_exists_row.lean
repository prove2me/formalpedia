-- Prove2me | Theorems.Thm_GlobalTheory_PeriodOnto_exists_row
-- name    : GlobalTheory.PeriodOnto.exists_row
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:35.098229+00:00
-- url     : https://prove2.me/theorems/5327134e-911e-4bd0-9e50-ed8a019d00ef
-- title:
--   Period Onto: exists row
-- statement:
--   The Period Onto construction uses the exists row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L361-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L361-L371

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.PeriodOnto.exists_row {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {r : ℕ} (φ : Λ →ₗ[𝓞 E] (Fin r → E))
    (hinj : Function.Injective φ) (hsp : Submodule.span E (Set.range φ) = ⊤) (σ : E →+* ℂ) (f : Λ →+ ℂ)
    (hf : ∀ (a : 𝓞 E) x, f (a • x) = σ (a : E) * f x) :
    ∃ c : Fin r → ℂ, ∀ v, f v = ∑ j, c j * σ (φ v j) := by sorry
