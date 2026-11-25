-- Prove2me | Theorems.Thm_GlobalTheory_exists_level_goodAt_all_primes_and_idx
-- name    : GlobalTheory.exists_level_goodAt_all_primes_and_idx
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:13.615442+00:00
-- url     : https://prove2.me/theorems/196cd6d5-128d-5f7c-a7a8-7bafdca76cbc
-- title:
--   Global Theory: exists level good At all primes and idx
-- statement:
--   The Global Theory construction uses the exists level good At all primes and idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelGoodAtAllPrimesAndIdx.lean#L116-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelGoodAtAllPrimesAndIdx.lean#L116-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLevelGoodAtAllPrimesAndIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.exists_level_goodAt_all_primes_and_idx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (A : ℕ), 0 < A →
      ∃ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.A = A ∧ (∀ p : ℕ, p.Prime → l.GoodAt p) ∧
        ∀ p : ℕ, p.Prime → ∃ i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Idx H p, i.l = l := by sorry
