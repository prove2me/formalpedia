-- Prove2me | Theorems.Thm_GlobalTheory_CoveringCompare_splitOver_of_torusExtension
-- name    : GlobalTheory.CoveringCompare.splitOver_of_torusExtension
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:42.739454+00:00
-- url     : https://prove2.me/theorems/508ff111-ab7b-4052-a872-1646d7581d9d
-- title:
--   Covering Compare: split Over of torus Extension
-- statement:
--   The Covering Compare construction uses the split Over of torus Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoveringAndSmoothnessIffOfSeparableSplitting.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoveringAndSmoothnessIffOfSeparableSplitting.lean#L26-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoveringCompare
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke

theorem GlobalTheory.CoveringCompare.splitOver_of_torusExtension {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by sorry
