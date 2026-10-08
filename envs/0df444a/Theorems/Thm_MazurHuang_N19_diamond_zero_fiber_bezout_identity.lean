-- Prove2me | Theorems.Thm_MazurHuang_N19_diamond_zero_fiber_bezout_identity
-- name    : MazurHuang.N19.diamond_zero_fiber_bezout_identity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:33.639873+00:00
-- url     : https://prove2.me/theorems/ee842dbf-6f03-4735-9d40-1901f07ca50f
-- title:
--   The zero-fibre Bézout identity
-- statement:
--   The explicit Bézout combination of the optimized plane equation and the first quotient-coordinate numerator equals x⁷(x+1)².
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:24-40; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:52-58; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:63-64; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:67-68; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:71-72; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:75-76; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:79-80; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:210-215; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:218-223; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:226-227; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:230-231; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:234-235; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:238-249; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:266-270; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:274-280; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:282-290

import Mathlib

theorem MazurHuang.N19.diamond_zero_fiber_bezout_identity (x y : ℚ) :
    (fun (x y : ℚ) => (x ^ 2 - x - 1) * y ^ 3
      + (-x ^ 4 + x ^ 3 - x) * y ^ 2
      + (-2 * x ^ 5 - x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 7 + 2 * x ^ 6 + 2 * x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2) x y * (fun (x y : ℚ) => y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2) x y +
        (fun (x y : ℚ) => (-x ^ 2 + x + 1) * y ^ 4
      + (x ^ 4 - x ^ 3 + x ^ 2 - 1) * y ^ 3
      + (2 * x ^ 5 - 3 * x ^ 3 - 4 * x ^ 2 - 2 * x) * y ^ 2
      + (-x ^ 7 - 2 * x ^ 6 - 4 * x ^ 5 - x ^ 4 +
          4 * x ^ 3 + 2 * x ^ 2) * y
      + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2) x y * (fun (x y : ℚ) => y ^ 4
      - (x ^ 2 + 1) * y ^ 3
      - x * (2 * x ^ 2 + 3 * x + 1) * y ^ 2
      + x ^ 2 * (x ^ 3 + 3 * x ^ 2 + 5 * x + 4) * y
      - x ^ 2 * (x + 1)) x y =
      x ^ 7 * (x + 1) ^ 2 := by sorry
