-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_thH_deg_zero
-- name    : GlobalTheory.SW.Base.thH_deg_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:13.876692+00:00
-- url     : https://prove2.me/theorems/3eb05322-4712-48fb-a771-b82babbfb0e1
-- title:
--   Base: th H deg zero
-- statement:
--   The Base construction uses the th H deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L451-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L451-L455

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

theorem GlobalTheory.SW.Base.thH_deg_zero (φ : Matrix (Fin n) (Fin 0) E → ℂ) (Z : CM Ψ 0 0) (z z' : CM Ψ n 0) :
    thH Ψ φ Z z z' = φ 0 := by sorry
