-- Prove2me | Theorems.Thm_GlobalTheory_AbTan_lifts_const
-- name    : GlobalTheory.AbTan.lifts_const
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:09.178126+00:00
-- url     : https://prove2.me/theorems/cec949ac-8701-4503-8f79-5260e071cf32
-- title:
--   Ab Tan: lifts const
-- statement:
--   The Ab Tan construction uses the lifts const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HopfLaurent.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HopfLaurent.lean#L50-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HopfLaurent
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
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbTan
variable {R : Type} [CommRing R]

theorem GlobalTheory.AbTan.lifts_const {X : Scheme.{0}} (s : X ⟶ Sp R) {B : Type} (M : Type) [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (h : P ≫ s = spMap (algebraMap R B)) :
    Lifts s P (spMap (TrivSqZeroExt.inlHom B M) ≫ P) := by sorry
