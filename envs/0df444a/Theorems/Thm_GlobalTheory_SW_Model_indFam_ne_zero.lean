-- Prove2me | Theorems.Thm_GlobalTheory_SW_Model_indFam_ne_zero
-- name    : GlobalTheory.SW.Model.indFam_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:51.722177+00:00
-- url     : https://prove2.me/theorems/08f98d47-c3be-4d5f-86b6-3e2e6ed7eb7f
-- title:
--   Model: ind Fam ne zero
-- statement:
--   The Model construction uses the ind Fam ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L122-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L122-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.Model.indFam_ne_zero (n N M : ℕ) : ∃ Λ ∈ Vset E n M, indFam E n N Λ 0 = 1 := by sorry
