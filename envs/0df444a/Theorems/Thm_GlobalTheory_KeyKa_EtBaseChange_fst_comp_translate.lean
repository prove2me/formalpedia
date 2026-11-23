-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_fst_comp_translate
-- name    : GlobalTheory.KeyKa.EtBaseChange.fst_comp_translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:49.529796+00:00
-- url     : https://prove2.me/theorems/0c1c7ab3-dcda-45b3-b3d7-1fa715769bd0
-- title:
--   Et Base Change: fst comp translate
-- statement:
--   The Et Base Change construction uses the fst comp translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L84-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L84-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem GlobalTheory.KeyKa.EtBaseChange.fst_comp_translate (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ((toUnit (epsR R) ≫ z) * v).left = z.left := by sorry
