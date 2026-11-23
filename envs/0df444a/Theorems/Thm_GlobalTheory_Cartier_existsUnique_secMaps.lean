-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_existsUnique_secMaps
-- name    : GlobalTheory.Cartier.existsUnique_secMaps
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:54.589405+00:00
-- url     : https://prove2.me/theorems/2c31e420-7fce-4f0e-98fa-357b1a38635d
-- title:
--   Cartier: exists Unique sec Maps
-- statement:
--   The Cartier construction uses the exists Unique sec Maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L276-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L276-L283

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.Cartier.existsUnique_secMaps {A B : LB X} {a : A.Sec} {b : B.Sec} (ha : IsRegularSec a)
    (h : ∀ (p : B.ι) (q : A.ι), Associated (resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) (b.f p))) :
    ∃! w : LB.Iso A B, w.IsGen ∧ SecMaps w a b := by sorry
