-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningDetermines_eq_zero_of_secIdeal_eq_bot
-- name    : GlobalTheory.ThickeningDetermines.eq_zero_of_secIdeal_eq_bot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:25:10.632806+00:00
-- url     : https://prove2.me/theorems/119a6dc1-23ef-4061-a1e8-8ab8ddb2ac5d
-- title:
--   Thickening Determines: eq zero of sec Ideal eq bot
-- statement:
--   The Thickening Determines construction uses the eq zero of sec Ideal eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroAndHomEqOfThickenings.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroAndHomEqOfThickenings.lean#L49-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningDetermines
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
variable {X Y : Scheme.{0}} {N : LB X}

theorem GlobalTheory.ThickeningDetermines.eq_zero_of_secIdeal_eq_bot (hN : N.IsLB) (s : N.Sec) (h : secIdeal hN s = ⊥) (j : N.ι) :
    s.f j = 0 := by sorry
