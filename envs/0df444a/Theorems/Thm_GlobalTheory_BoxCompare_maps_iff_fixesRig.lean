-- Prove2me | Theorems.Thm_GlobalTheory_BoxCompare_maps_iff_fixesRig
-- name    : GlobalTheory.BoxCompare.maps_iff_fixesRig
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:01:18.891452+00:00
-- url     : https://prove2.me/theorems/4611e816-cdb2-4f9d-8e39-a16679863de8
-- title:
--   Box Compare: maps iff fixes Rig
-- statement:
--   The Box Compare construction uses the maps iff fixes Rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L220-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L220-L263

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxCompare
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.BoxCompare.maps_iff_fixesRig (L : LB G.left) (r : LB.Gen (L.pull (eSec G)))
    (sy : SymGen L (ι[G]).left) :
    LB.Gen.Maps (LB.linCombIso (symEquiv L _ sy) (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1))
        r (rigPullOf (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L r) ↔
      FixesRig L (ι[G]).left (eSec G) sy r := by sorry
