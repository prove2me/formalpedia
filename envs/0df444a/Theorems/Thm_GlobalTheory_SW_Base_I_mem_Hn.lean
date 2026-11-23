-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_I_mem_Hn
-- name    : GlobalTheory.SW.Base.I_mem_Hn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:03.48023+00:00
-- url     : https://prove2.me/theorems/94a72c73-730c-4606-8994-f2bfabfe71ef
-- title:
--   Base: I mem Hn
-- statement:
--   The Base construction uses the I mem Hn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L404-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L404-L413

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
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.Base.I_mem_Hn : (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) : CM Ψ N N) ∈ Hn Ψ N := by sorry
