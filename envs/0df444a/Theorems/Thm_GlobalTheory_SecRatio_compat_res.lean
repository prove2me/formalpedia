-- Prove2me | Theorems.Thm_GlobalTheory_SecRatio_compat_res
-- name    : GlobalTheory.SecRatio.compat_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:06:37.434816+00:00
-- url     : https://prove2.me/theorems/73bcf010-2050-49ee-9d89-2caeb8bf92ac
-- title:
--   Sec Ratio: compat res
-- statement:
--   The Sec Ratio construction uses the compat res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueIsRatio.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueIsRatio.lean#L23-L28

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

theorem GlobalTheory.SecRatio.compat_res (s : H.Sec) (i j : H.ι) {V : X.Opens} (hi : V ≤ H.U i) (hj : V ≤ H.U j) :
    resG X hi (s.f i) = resG X (le_inf hi hj) (H.g i j : Γ(X, H.U i ⊓ H.U j)) * resG X hj (s.f j) := by sorry
