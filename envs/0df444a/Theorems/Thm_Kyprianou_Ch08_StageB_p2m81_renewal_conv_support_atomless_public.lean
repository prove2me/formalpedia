-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_renewal_conv_support_atomless_public
-- name    : Kyprianou.Ch08.StageB.p2m81_renewal_conv_support_atomless_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:11:29.222807+00:00
-- url     : https://prove2.me/theorems/be824e14-d7bb-4f67-8550-83f454974807
-- title:
--   Convolution preserves nonneg support and right atomlessness
-- statement:
--   Additive convolution of s-finite real measures preserves support on [0,oo) and preserves atomlessness from the right factor: if both factors vanish on Iio 0 so does the convolution, and if the right factor has no atoms neither does the convolution.
-- source:
--   Decomposition of Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap (1683b347-a85a-4b0e-b47b-61a14cca75e1): source-faithful public child for code-budget split (167 lines/6157 tokens exceed 100/2500 caps). Generic measure step discharging hconvSupp/hconv2/hmsupp/hnu-supp/hmatom/hρmatom in the parent renewal construction.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_renewal_conv_support_atomless_public
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    (μ (Iio (0:ℝ)) = 0 → ν (Iio (0:ℝ)) = 0 → (μ.conv ν) (Iio (0:ℝ)) = 0) ∧
    ((∀ y : ℝ, ν {y} = 0) → ∀ x : ℝ, (μ.conv ν) {x} = 0) := by sorry
