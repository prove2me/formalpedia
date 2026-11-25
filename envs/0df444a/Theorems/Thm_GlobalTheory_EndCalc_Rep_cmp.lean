-- Prove2me | Theorems.Thm_GlobalTheory_EndCalc_Rep_cmp
-- name    : GlobalTheory.EndCalc.Rep.cmp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:58:02.583862+00:00
-- url     : https://prove2.me/theorems/8e68ddbc-8e75-4a52-a7dd-8387387fa986
-- title:
--   Rep: cmp
-- statement:
--   The Rep construction uses the cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UniformizationEndomorphismCalculus.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UniformizationEndomorphismCalculus.lean#L68-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
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
noncomputable section
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
open FreeAbelianGroup
variable {D : DegPre R} {T₀ : Over (Spec (CommRingCat.of R))}

theorem GlobalTheory.EndCalc.Rep.cmp {a : D.P.A ⟶ D.P.A} {p χ : D.X} {u : CmpGen D a p χ} (hu : Normd u) (x : T₀ ⟶ D.P.A) :
    Rep (of (cP D T₀ p * x) - of (cP D T₀ p) - of x - of (cP D T₀ χ * (x ≫ a)) + of (cP D T₀ χ) + of (x ≫ a))
      fun _ ρ z J => val u (ρ ≫ x).left z J := by sorry
