-- Prove2me | Theorems.Thm_GlobalTheory_SW_Model_admissible_scaled_lattice_family
-- name    : GlobalTheory.SW.Model.admissible_scaled_lattice_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:37.613344+00:00
-- url     : https://prove2.me/theorems/1990c80a-1b7c-4fa6-819e-f095a4ed8297
-- title:
--   Model: admissible scaled lattice family
-- statement:
--   The Model construction uses the admissible scaled lattice family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L318-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L318-L336

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

theorem GlobalTheory.SW.Model.admissible_scaled_lattice_family {n N M R : ℕ} (hM : 0 < M) (hR : 0 < R) : admitted M R (divFam E n N R) := by sorry
