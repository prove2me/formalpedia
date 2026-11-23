-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_germK_eq_mul_ratOf
-- name    : GlobalTheory.Cartier.germK_eq_mul_ratOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:43.515792+00:00
-- url     : https://prove2.me/theorems/61d7c69f-3ff5-4939-9c01-9ce84372f550
-- title:
--   Cartier: germ K eq mul rat Of
-- statement:
--   The Cartier construction uses the germ K eq mul rat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L507-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L507-L526

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
variable [IsIntegral X]

theorem GlobalTheory.Cartier.germK_eq_mul_ratOf {L : LB X} (hL : L.IsLB) {s : L.Sec} (hs : IsRegularSec s)
    (V : X.Opens) [Nonempty V] {t : ∀ i, Γ(X, V ⊓ L.U i)} (ht : t ∈ secOn L V) (i : L.ι)
    [Nonempty (V ⊓ L.U i : X.Opens)] :
    (X.germToFunctionField _).hom (t i) =
      (X.germToFunctionField (V ⊓ L.U i)).hom (resG X inf_le_right (s.f i)) * ratOf hL s V t := by sorry
