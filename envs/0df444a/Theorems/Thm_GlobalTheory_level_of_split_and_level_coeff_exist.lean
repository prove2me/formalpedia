-- Prove2me | Theorems.Thm_GlobalTheory_level_of_split_and_level_coeff_exist
-- name    : GlobalTheory.level_of_split_and_level_coeff_exist
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:02.021114+00:00
-- url     : https://prove2.me/theorems/0f293e9f-a2e6-4bab-9d1b-7426633b5bda
-- title:
--   Global Theory: level of split and level coeff exist
-- statement:
--   The Global Theory construction uses the level of split and level coeff exist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LevelOfSplitAndLevelCoeffExist.lean#L116-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LevelOfSplitAndLevelCoeffExist.lean#L116-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.level_of_split_and_level_coeff_exist :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (al : 𝓞 E) (M A : ℕ),
      al ∈ Algebra.adjoin ℤ {H.w0} → al * H.bar al = (M : 𝓞 E) → IsCoprime al (H.bar al) → 3 ≤ M →
      Odd M → 0 < A → ∃ l : Level H, l.M = M ∧ l.A = A ∧ l.Mb = Ideal.span {H.bar al}) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Nonempty (Level H)) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H),
      Nonempty (Coeff l) := by sorry
