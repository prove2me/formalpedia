-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_SecOn_existsUnique_of_local
-- name    : GlobalTheory.AbLaw.SecOn.existsUnique_of_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:24.31285+00:00
-- url     : https://prove2.me/theorems/187c51aa-eb8b-4c4d-9af4-2768a5ed26f0
-- title:
--   Sec On: exists Unique of local
-- statement:
--   The Sec On construction uses the exists Unique of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L106-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L106-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
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
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}

theorem GlobalTheory.AbLaw.SecOn.existsUnique_of_local (hM : M.IsLB) {I : Type} (O : I → X.Opens) (hO : ∀ a, O a ≤ V)
    (hc : V ≤ ⨆ a, O a) (c : I → M.ι) (hU : ∀ a, O a ≤ M.U (c a)) (x : ∀ a, Γ(X, O a))
    (h : ∀ a b, rs X (inf_le_left : O a ⊓ O b ≤ O a) (x a) =
      rs X (inf_le_inf (hU a) (hU b)) (M.g (c a) (c b)).val *
        rs X (inf_le_right : O a ⊓ O b ≤ O b) (x b)) :
    ∃! t : SecOn M V, ∀ a, rs X (le_inf (hO a) (hU a)) (coord t (c a)) = x a := by sorry
