-- Prove2me | Theorems.Thm_GlobalTheory_SW_Model_not_admissible_half_lattice_family
-- name    : GlobalTheory.SW.Model.not_admissible_half_lattice_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:49.177271+00:00
-- url     : https://prove2.me/theorems/72898695-602a-48d3-8490-0eb7e58ffb3b
-- title:
--   Model: not admissible half lattice family
-- statement:
--   The Model construction uses the not admissible half lattice family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L338-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L338-L354

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

theorem GlobalTheory.SW.Model.not_admissible_half_lattice_family {n N M : ℕ} : ¬ admitted M 1 (divFam E (n + 1) (N + 1) 2) := by sorry
