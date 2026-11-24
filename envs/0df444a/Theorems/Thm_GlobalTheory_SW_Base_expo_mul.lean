-- Prove2me | Theorems.Thm_GlobalTheory_SW_Base_expo_mul
-- name    : GlobalTheory.SW.Base.expo_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:42.701794+00:00
-- url     : https://prove2.me/theorems/3c4c429c-8cec-4101-ae49-396be8a96591
-- title:
--   Base: expo mul
-- statement:
--   The Base construction uses the expo mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L309-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean#L309-L325

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

theorem GlobalTheory.SW.Base.expo_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ (h * x) Z z z' =
      expo Ψ x Z (fun τ => (h.map τ.1)ᵀ * z τ) (fun τ => (h.map τ.1)ᴴ * z' τ) := by sorry
