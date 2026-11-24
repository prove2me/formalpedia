-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_map_eq_sum_repr
-- name    : GlobalTheory.AnArc.map_eq_sum_repr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:30.452639+00:00
-- url     : https://prove2.me/theorems/117ba4a2-4c7c-4347-9048-3737d508e843
-- title:
--   An Arc: map eq sum repr
-- statement:
--   The An Arc construction uses the map eq sum repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L258-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L258-L261

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.map_eq_sum_repr {M : Type} [Ring M] (f : A.X →+ M) (y : A.X) :
    f y = ∑ i, ((Module.Free.chooseBasis ℤ A.X).repr y i : M) * f (Module.Free.chooseBasis ℤ A.X i) := by sorry
