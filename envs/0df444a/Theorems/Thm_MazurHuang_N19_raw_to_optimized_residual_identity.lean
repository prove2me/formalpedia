-- Prove2me | Theorems.Thm_MazurHuang_N19_raw_to_optimized_residual_identity
-- name    : MazurHuang.N19.raw_to_optimized_residual_identity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:37.541088+00:00
-- url     : https://prove2.me/theorems/7303decb-d2cf-45f0-81fa-f078a283d378
-- title:
--   Residual identity for the raw-to-optimized chart
-- statement:
--   The displayed rational chart transports the raw order-nineteen equation to the optimized plane equation, with an explicit residual factor.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:24-40; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:52-58; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:63-64; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:67-68; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:71-72; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:75-76; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:79-80; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:210-215; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:218-223; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:226-227; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:230-231; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:234-235; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:238-249; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:266-270; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:274-280; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:179-196

import Mathlib

theorem MazurHuang.N19.raw_to_optimized_residual_identity {r s : ℚ}
    (hrs : r - s ≠ 0) (hdelta : (fun (r s : ℚ) => r * s ^ 2 - 3 * r * s + r + s ^ 2) r s ≠ 0) :
    (fun (x y : ℚ) => y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2) ((fun (r s : ℚ) => -(s - 1) * (fun (r s : ℚ) => r * s - 2 * r + 1) r s / (fun (r s : ℚ) => r * s ^ 2 - 3 * r * s + r + s ^ 2) r s) r s) ((fun (r s : ℚ) => (s - 1) * (fun (r s : ℚ) => r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) r s / ((r - s) * (fun (r s : ℚ) => r * s ^ 2 - 3 * r * s + r + s ^ 2) r s)) r s) =
      (s - 1) ^ 2 * (s ^ 2 - r - s + 1) ^ 2 *
          (fun (r s : ℚ) => r * s - 2 * r + 1) r s ^ 4 /
        ((s - r) ^ 5 * (fun (r s : ℚ) => r * s ^ 2 - 3 * r * s + r + s ^ 2) r s ^ 7) * (fun (r s : ℚ) => r ^ 6
      - r ^ 5 * s ^ 7 + 11 * r ^ 5 * s ^ 6 - 48 * r ^ 5 * s ^ 5
      + 105 * r ^ 5 * s ^ 4 - 121 * r ^ 5 * s ^ 3
      + 69 * r ^ 5 * s ^ 2 - 20 * r ^ 5 * s - r ^ 5
      - 2 * r ^ 4 * s ^ 7 + 12 * r ^ 4 * s ^ 6 - 9 * r ^ 4 * s ^ 5
      - 60 * r ^ 4 * s ^ 4 + 144 * r ^ 4 * s ^ 3
      - 105 * r ^ 4 * s ^ 2 + 35 * r ^ 4 * s
      - 3 * r ^ 3 * s ^ 7 + 3 * r ^ 3 * s ^ 6 + 21 * r ^ 3 * s ^ 5
      - 30 * r ^ 3 * s ^ 4 - 41 * r ^ 3 * s ^ 3
      + 51 * r ^ 3 * s ^ 2 - 21 * r ^ 3 * s
      + r ^ 2 * s ^ 9 - 6 * r ^ 2 * s ^ 8 + 21 * r ^ 2 * s ^ 7
      - 50 * r ^ 2 * s ^ 6 + 66 * r ^ 2 * s ^ 5
      - 31 * r ^ 2 * s ^ 4 + 25 * r ^ 2 * s ^ 3
      - 18 * r ^ 2 * s ^ 2 + 7 * r ^ 2 * s
      + 3 * r * s ^ 6 - 15 * r * s ^ 5 + 10 * r * s ^ 4
      - 6 * r * s ^ 3 + 3 * r * s ^ 2 - r * s + s ^ 6) r s := by sorry
