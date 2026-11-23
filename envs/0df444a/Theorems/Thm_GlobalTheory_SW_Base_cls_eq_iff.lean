-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_cls_eq_iff
-- name    : GlobalTheory.SW.Base.cls_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:48.235748+00:00
-- url     : https://prove2.me/theorems/838cb3bc-4a2c-4026-9a9a-4ead5c7b82d9
-- title:
--   Base: cls eq iff
-- statement:
--   The Base construction uses the cls eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L259-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L259-L265

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

theorem GlobalTheory.SW.Base.cls_eq_iff {M : ℕ} (Λ Λ' : Vset E n M) :
    (Quot.mk _ Λ : Cls E n M) = Quot.mk _ Λ' ↔ ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1 := by sorry
