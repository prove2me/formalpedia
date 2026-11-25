-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_ratOf_smul
-- name    : GlobalTheory.Cartier.ratOf_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:35.412069+00:00
-- url     : https://prove2.me/theorems/60627385-3c42-5465-810a-936ea4bb2738
-- title:
--   Cartier: rat Of smul
-- statement:
--   The Cartier construction uses the rat Of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L498-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L498-L505

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

theorem GlobalTheory.Cartier.ratOf_smul {L : LB X} (hL : L.IsLB) (s : L.Sec) (V : X.Opens) [Nonempty V] (c : Γ(X, V))
    (t : ∀ i, Γ(X, V ⊓ L.U i)) :
    ratOf hL s V (fun i => resG X inf_le_left c * t i) = c • ratOf hL s V t := by sorry
