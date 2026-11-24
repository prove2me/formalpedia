-- Prove2me | Theorems.Thm_GlobalTheory_AdicSum_sumI_add
-- name    : GlobalTheory.AdicSum.sumI_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:55:27.351406+00:00
-- url     : https://prove2.me/theorems/7fca8a6c-b079-4d0a-9b59-85f032fef762
-- title:
--   Adic Sum: sum I add
-- statement:
--   The Adic Sum construction uses the sum I add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SumFCalculus.lean#L79-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SumFCalculus.lean#L79-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SumFCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
open GlobalTheory GlobalTheory.AdicSum
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']

theorem GlobalTheory.AdicSum.sumI_add {x x' : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x' s') :
    _root_.GlobalTheory.UT.SumI I (fun i => x i + x' i) (s + s') := by sorry
