-- Prove2me | Theorems.Thm_GlobalTheory_LevelAllPrimes_isCoprime_add_rt_sub_rt
-- name    : GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:02:57.661453+00:00
-- url     : https://prove2.me/theorems/a3500f47-5086-4810-9577-2062873a3e84
-- title:
--   Level All Primes: is Coprime add rt sub rt
-- statement:
--   The Level All Primes construction uses the is Coprime add rt sub rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelGoodAtAllPrimesAndIdx.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelGoodAtAllPrimesAndIdx.lean#L32-L45

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
open GlobalTheory GlobalTheory.LevelAllPrimes
open GlobalTheory.HostModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {c : ℕ} (hc : Nat.Coprime c H.d)
    (ho : Odd (c ^ 2 + H.d)) :
    IsCoprime ((c : 𝓞 E) + H.rt) (c - H.rt) := by sorry
