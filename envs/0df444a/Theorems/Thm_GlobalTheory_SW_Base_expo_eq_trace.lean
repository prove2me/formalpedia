-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_expo_eq_trace
-- name    : GlobalTheory.SW.Base.expo_eq_trace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:38.701154+00:00
-- url     : https://prove2.me/theorems/781e9767-71e2-421c-af29-2dd2f937bc44
-- title:
--   Base: expo eq trace
-- statement:
--   The Base construction uses the expo eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L299-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L299-L307

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
omit [IsCMField E]

theorem GlobalTheory.SW.Base.expo_eq_trace (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ x Z z z' = ∑ τ : Ψ, ((x.map τ.1 * Z τ * (x.map τ.1)ᴴ).trace +
      (x.map τ.1 * (z τ)ᵀ).trace + (z' τ * (x.map τ.1)ᴴ).trace) := by sorry
