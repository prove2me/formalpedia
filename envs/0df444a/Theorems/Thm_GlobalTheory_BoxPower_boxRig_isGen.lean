-- Prove2me | Theorems.Thm_GlobalTheory_BoxPower_boxRig_isGen
-- name    : GlobalTheory.BoxPower.boxRig_isGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:09.776273+00:00
-- url     : https://prove2.me/theorems/90c0261d-6ecc-494d-abd0-db70e0d3194b
-- title:
--   Box Power: box Rig is Gen
-- statement:
--   The Box Power construction uses the box Rig is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxPowerBasic.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxPowerBasic.lean#L72-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxPowerBasic
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
noncomputable section
open GlobalTheory GlobalTheory.BoxPower
variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}

theorem GlobalTheory.BoxPower.boxRig_isGen [IsCommMonObj G'] [IsCommMonObj G] (p : Out.IsPowGrp G' G j) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) : (Out.boxRig p L r).IsGen := by sorry
