-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_moves_ccT
-- name    : GlobalTheory.SW.Base.moves_ccT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:37.893631+00:00
-- url     : https://prove2.me/theorems/77e24174-ed7c-41c2-ab82-925b0e0fb15a
-- title:
--   Base: moves cc T
-- statement:
--   The Base construction uses the moves cc T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L255-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L255-L257

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

theorem GlobalTheory.SW.Base.moves_ccT {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) {Λ Λ' : Lt E n}
    (h1 : Moves h Λ Λ') : Moves (ccT h) Λ' Λ := by sorry
