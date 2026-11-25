-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_classSum_eq
-- name    : GlobalTheory.SW.Base.classSum_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:07.087413+00:00
-- url     : https://prove2.me/theorems/cc68ac3b-b3b1-4c5b-a486-867c365b78a5
-- title:
--   Base: class Sum eq
-- statement:
--   The Base construction uses the class Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L286-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L286-L291

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

theorem GlobalTheory.SW.Base.classSum_eq {M : ℕ} {f : Lt E n → ℂ} (hf : IsClassFn M f) (s : Cls E n M → Vset E n M)
    (hs : ∀ c, Quot.mk _ (s c) = c) :
    classSum M f = ∑ᶠ c : Cls E n M, (wt M (s c).1 : ℂ) * f (s c).1 := by sorry
