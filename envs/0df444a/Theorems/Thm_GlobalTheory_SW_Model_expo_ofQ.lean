-- Prove2me | Theorems.Thm_GlobalTheory_SW_Model_expo_ofQ
-- name    : GlobalTheory.SW.Model.expo_ofQ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:15.452163+00:00
-- url     : https://prove2.me/theorems/73744031-a58e-593e-b23c-64ed1396e066
-- title:
--   Model: expo of Q
-- statement:
--   The Model construction uses the expo of Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L205-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean#L205-L256

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
omit [IsCMField E]

theorem GlobalTheory.SW.Model.expo_ofQ (Ψ : Finset (E →+* ℂ)) {n N : ℕ} (m : Matrix (Fin n) (QI E N) ℚ) (Z : CM Ψ N N)
    (z z' : CM Ψ n N) :
    ∑ k, (qv (m k) ⬝ᵥ tauOf Ψ Z *ᵥ qv (m k) + 2 * (qv (m k) ⬝ᵥ zetaOf Ψ z z' k)) =
      2 * expo Ψ (ofQ m) Z z z' := by sorry
