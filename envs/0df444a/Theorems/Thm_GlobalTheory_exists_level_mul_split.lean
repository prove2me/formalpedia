-- Prove2me | Theorems.Thm_GlobalTheory_exists_level_mul_split
-- name    : GlobalTheory.exists_level_mul_split
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:53.540012+00:00
-- url     : https://prove2.me/theorems/e2893ac1-cb31-5003-9fe7-2f92a779312e
-- title:
--   Global Theory: exists level mul split
-- statement:
--   The Global Theory construction uses the exists level mul split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelMulSplit.lean#L118-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelMulSplit.lean#L118-L253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLevelMulSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open NumberField Pointwise

theorem GlobalTheory.exists_level_mul_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H), (∀ (pd : ℕ) (I : Ideal (𝓞 E)), Odd pd → pd.Coprime l.M → I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {H.w0}} → I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} → I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∃ l₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.Dvd l₂ ∧ l₂.M = l.M * pd ∧ l₂.Mb = l.Mb * I ∧ l₂.A = l.A) ∧ ∀ pd : ℕ, pd.Prime → pd ≠ 2 → jacobiSym (-(H.d : ℤ)) pd = 1 → ∃ I : Ideal (𝓞 E), I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {H.w0}} ∧ I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} ∧ I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by sorry
