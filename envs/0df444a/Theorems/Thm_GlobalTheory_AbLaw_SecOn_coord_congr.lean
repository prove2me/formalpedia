-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_SecOn_coord_congr
-- name    : GlobalTheory.AbLaw.SecOn.coord_congr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:43.29027+00:00
-- url     : https://prove2.me/theorems/9a080f94-3278-419b-b29e-b3a8d973368b
-- title:
--   Sec On: coord congr
-- statement:
--   The Sec On construction uses the coord congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L137-L142

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

theorem GlobalTheory.AbLaw.SecOn.coord_congr (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) (s : SecOn L V)
    (p : M.ι) (q : L.ι) {O : X.Opens} (hp : O ≤ V ⊓ M.U p) (hq : O ≤ V ⊓ L.U q)
    (h : O ≤ M.U p ⊓ L.U q) :
    rs X hp (coord (congr hL hM w hw V s) p) =
      rs X h (show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)).val * rs X hq (coord s q) := by sorry
