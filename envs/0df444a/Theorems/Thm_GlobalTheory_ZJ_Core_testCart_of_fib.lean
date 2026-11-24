-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_Core_testCart_of_fib
-- name    : GlobalTheory.ZJ.Core.testCart_of_fib
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:02:49.445403+00:00
-- url     : https://prove2.me/theorems/0972fd2c-f27c-4125-bd2a-4fa91938bec8
-- title:
--   Core: test Cart of fib
-- statement:
--   The Core construction uses the test Cart of fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L113-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L113-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ

theorem GlobalTheory.ZJ.Core.testCart_of_fib :
    ∀ C : Core, C.Fib → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart := by sorry
