-- Prove2me | Theorems.Thm_GlobalTheory_SecRatio_isUnit_res
-- name    : GlobalTheory.SecRatio.isUnit_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:23.802414+00:00
-- url     : https://prove2.me/theorems/ed5eee81-d310-4f8a-af2d-cf8f8aa86c56
-- title:
--   Sec Ratio: is Unit res
-- statement:
--   The Sec Ratio construction uses the is Unit res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueIsRatio.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueIsRatio.lean#L30-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.SecRatio
variable {X : Scheme.{0}} {H : LB X}

theorem GlobalTheory.SecRatio.isUnit_res (t : H.Sec) (l : H.ι) {V : X.Opens} (hV : V ≤ Out.nonzeroLocus t)
    (hl : V ≤ H.U l) : IsUnit (resG X hl (t.f l)) := by sorry
