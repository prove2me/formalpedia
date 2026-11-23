-- Prove2me | Theorems.Thm_GlobalTheory_MulFinite_gs_appLE
-- name    : GlobalTheory.MulFinite.gs_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:03.171479+00:00
-- url     : https://prove2.me/theorems/8e1fd704-367b-4f64-bb41-bd693ffe07d1
-- title:
--   Mul Finite: gs app LE
-- statement:
--   The Mul Finite construction uses the gs app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L83-L85

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

theorem GlobalTheory.MulFinite.gs_appLE {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (V : Z.Opens) (hle : V ≤ r ⁻¹ᵁ U)
    (h : z ∈ V) (a : Γ(Y, U)) : gs (𝟙 Z) z V ((r.appLE U V hle).hom a) = gs r z U a := by sorry
