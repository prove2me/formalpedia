-- Prove2me | Theorems.Thm_GlobalTheory_BoxPower_boxPower_basic
-- name    : GlobalTheory.BoxPower.boxPower_basic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:15.248775+00:00
-- url     : https://prove2.me/theorems/45cb3acd-1133-4e7d-aadd-90e305be8cc5
-- title:
--   Box Power: box Power basic
-- statement:
--   The Box Power construction uses the box Power basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxPowerBasic.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxPowerBasic.lean#L96-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxPowerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm

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

theorem GlobalTheory.BoxPower.boxPower_basic : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ), (Out.boxLB P.L (Out.powPr P.A (n := j))).IsLB ∧ Out.Sym (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) ∧ ∀ rig : LB.Gen (P.L.pull (eSec P.A)), rig.IsGen → (haveI := P.isAb.comm; (Out.boxRig (Out.powIsPowGrp P.A j) P.L rig).IsGen) := by sorry
