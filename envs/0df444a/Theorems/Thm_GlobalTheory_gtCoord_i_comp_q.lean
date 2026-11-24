-- Prove2me | Theorems.Thm_GlobalTheory_gtCoord_i_comp_q
-- name    : GlobalTheory.gtCoord_i_comp_q
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:18.657947+00:00
-- url     : https://prove2.me/theorems/27be7751-69eb-4b22-8721-730a0b38ad18
-- title:
--   Global Theory: gt Coord i comp q
-- statement:
--   The Global Theory construction uses the gt Coord i comp q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UnifPreAbelianPartIso.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UnifPreAbelianPartIso.lean#L15-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnifPreAbelianPartIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.gtCoord_i_comp_q {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    g'.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by sorry
