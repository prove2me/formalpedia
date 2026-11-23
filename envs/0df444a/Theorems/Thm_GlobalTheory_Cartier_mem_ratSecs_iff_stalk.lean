-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_mem_ratSecs_iff_stalk
-- name    : GlobalTheory.Cartier.mem_ratSecs_iff_stalk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:05.625266+00:00
-- url     : https://prove2.me/theorems/38cb6bbc-d43e-4f8e-88ac-590c239083b4
-- title:
--   Cartier: mem rat Secs iff stalk
-- statement:
--   The Cartier construction uses the mem rat Secs iff stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L438-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L438-L457

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

theorem GlobalTheory.Cartier.mem_ratSecs_iff_stalk {L : LB X} (s : L.Sec) (V : X.Opens) [Nonempty V]
    (h : X.functionField) :
    h ∈ ratSecs s V ↔ ∀ (i : L.ι) (x : X) (_ : x ∈ V) (hx : x ∈ L.U i),
      algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ _ x hx).hom (s.f i)) * h ∈
        Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by sorry
