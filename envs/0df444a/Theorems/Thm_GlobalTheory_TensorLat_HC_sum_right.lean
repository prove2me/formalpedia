-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_HC_sum_right
-- name    : GlobalTheory.TensorLat.HC_sum_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:30:28.151417+00:00
-- url     : https://prove2.me/theorems/b90c212d-639d-4008-9c8b-9658366322b0
-- title:
--   Tensor Lat: HC sum right
-- statement:
--   The Tensor Lat construction uses the HC sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L85-L87

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

theorem GlobalTheory.TensorLat.HC_sum_right {κ : Type*} (s : Finset κ) (v : Fin n → EuclideanSpace ℂ ι)
    (w : κ → Fin n → EuclideanSpace ℂ ι) : HC v (∑ j ∈ s, w j) = ∑ j ∈ s, HC v (w j) := by sorry
