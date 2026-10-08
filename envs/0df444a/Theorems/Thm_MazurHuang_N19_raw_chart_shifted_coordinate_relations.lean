-- Prove2me | Theorems.Thm_MazurHuang_N19_raw_chart_shifted_coordinate_relations
-- name    : MazurHuang.N19.raw_chart_shifted_coordinate_relations
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:21.488168+00:00
-- url     : https://prove2.me/theorems/6d2d46ab-b763-4ab2-8008-f66ca7029096
-- title:
--   Relations for the shifted raw-chart coordinates
-- statement:
--   Writing T=s−1, A=r−s and F=rs−2r+1 gives N=(A+T)F−A², D=(T+1)F−TA, F=AT−A+T² and s²−r−s+1=T²−A.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:63-80

import Mathlib

theorem MazurHuang.N19.raw_chart_shifted_coordinate_relations (r s : ℚ) : (fun (r s : ℚ) => r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) r s = ((r-s)+(s-1))*(fun (r s : ℚ) => r * s - 2 * r + 1) r s-(r-s)^2 ∧ (fun (r s : ℚ) => r * s ^ 2 - 3 * r * s + r + s ^ 2) r s = ((s-1)+1)*(fun (r s : ℚ) => r * s - 2 * r + 1) r s-(s-1)*(r-s) ∧ (r-s)*(s-1)-(r-s)+(s-1)^2 = (fun (r s : ℚ) => r * s - 2 * r + 1) r s ∧ (s-1)^2-(r-s) = s^2-r-s+1 := by sorry
