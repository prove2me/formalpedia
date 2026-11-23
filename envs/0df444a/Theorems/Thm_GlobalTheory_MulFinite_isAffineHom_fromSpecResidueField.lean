-- Prove2me | Theorems.Thm_GlobalTheory_MulFinite_isAffineHom_fromSpecResidueField
-- name    : GlobalTheory.MulFinite.isAffineHom_fromSpecResidueField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:08.25492+00:00
-- url     : https://prove2.me/theorems/248d026b-41a0-4b80-9e8c-0ff4e73a490d
-- title:
--   Mul Finite: is Affine Hom from Spec Residue Field
-- statement:
--   The Mul Finite construction uses the is Affine Hom from Spec Residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L67-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial

theorem GlobalTheory.MulFinite.isAffineHom_fromSpecResidueField (Y : Scheme.{0}) (y : Y) :
    IsAffineHom (Y.fromSpecResidueField y) := by sorry
