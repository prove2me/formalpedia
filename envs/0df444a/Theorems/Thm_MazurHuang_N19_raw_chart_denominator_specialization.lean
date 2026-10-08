-- Prove2me | Theorems.Thm_MazurHuang_N19_raw_chart_denominator_specialization
-- name    : MazurHuang.N19.raw_chart_denominator_specialization
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:28.10321+00:00
-- url     : https://prove2.me/theorems/7d37217c-902f-4082-8a23-dc3d13883a00
-- title:
--   Specialization along the raw-chart denominator
-- statement:
--   Substitution r = −s²/(s²−3s+1) into the raw plane polynomial gives s³(s−1)¹⁸/(s²−3s+1)⁶.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:24-40; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:52-58; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:63-64; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:67-68; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:71-72; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:75-76; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:79-80; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:210-215; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:218-223; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:226-227; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:230-231; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:234-235; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:238-249; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:266-270; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:274-280; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:101-114

import Mathlib

theorem MazurHuang.N19.raw_chart_denominator_specialization (s : ℚ) (hsq : s ^ 2 - 3 * s + 1 ≠ 0) :
    (fun (r s : ℚ) => r ^ 6
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
      - 6 * r * s ^ 3 + 3 * r * s ^ 2 - r * s + s ^ 6) (-s ^ 2 / (s ^ 2 - 3 * s + 1)) s =
      s ^ 3 * (s - 1) ^ 18 / (s ^ 2 - 3 * s + 1) ^ 6 := by sorry
