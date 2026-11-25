-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_SecOn_mulSec_eq_smul
-- name    : GlobalTheory.AbLaw.SecOn.mulSec_eq_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:34.304627+00:00
-- url     : https://prove2.me/theorems/5b1c59eb-583e-46c1-bb32-f112ee4032d0
-- title:
--   Sec On: mul Sec eq smul
-- statement:
--   The Sec On construction uses the mul Sec eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L273-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L273-L281

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
variable {t : ℤ}

theorem GlobalTheory.AbLaw.SecOn.mulSec_eq_smul (s s' : LB.Sec H) (r : Γ(X, V))
    (h : ∀ k, rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s'.f k) =
      rs X inf_le_left r * rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k))
    (x : SecOn (tw M H t) V) : mulSec M t s' V x = r • mulSec M t s V x := by sorry
