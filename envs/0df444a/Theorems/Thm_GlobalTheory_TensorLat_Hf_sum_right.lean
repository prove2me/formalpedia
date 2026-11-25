-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_Hf_sum_right
-- name    : GlobalTheory.TensorLat.Hf_sum_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:29:23.007383+00:00
-- url     : https://prove2.me/theorems/2f8bcddd-117f-4d02-b521-b4fd62038a9a
-- title:
--   Tensor Lat: Hf sum right
-- statement:
--   The Tensor Lat construction uses the Hf sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L68-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
variable {ι : Type} [Fintype ι] {n : ℕ}

theorem GlobalTheory.TensorLat.Hf_sum_right {κ : Type*} (s : Finset κ) (v : EuclideanSpace ℂ ι)
    (w : κ → EuclideanSpace ℂ ι) : Hf v (∑ j ∈ s, w j) = ∑ j ∈ s, Hf v (w j) := by sorry
