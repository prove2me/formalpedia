-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_wt_moves
-- name    : GlobalTheory.SW.Base.wt_moves
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:37:46.994418+00:00
-- url     : https://prove2.me/theorems/3d309e18-7445-4b4d-b4e9-2b45aaf720ce
-- title:
--   Base: wt moves
-- statement:
--   The Base construction uses the wt moves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L267-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L267-L284

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

theorem GlobalTheory.SW.Base.wt_moves {M : ℕ} {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n M) {Λ Λ' : Lt E n}
    (m : Moves h Λ Λ') : wt M Λ' = wt M Λ := by sorry
